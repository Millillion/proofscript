// A small elaborator: the generated Lean subset (lean-syntax.ts) to kernel expressions.
//
// Lean elaborates ProofScript's generated source when proving. To check a certificate
// without Lean, ProofScript elaborates the *statements* itself (theorem types, definition
// signatures and equations, constructor types) and asks the kernel whether the
// certificate's declarations have exactly those types (definitional equality). Proofs are
// never elaborated: wherever the source has a proof, the elaborated term has a hole
// (`HOLE T`, an opaque proof of `T`), which proof irrelevance makes equal to any proof.
//
// Implicit arguments and instances are found by first-order unification, as in Lean, from
// a fixed table of instances. Whatever this elaborator cannot handle is an error: the
// declaration then needs Lean, it is never guessed.

import {
  type Environment,
  type Expr,
  type FVar,
  type Level,
  type Name,
  TypeChecker,
  KernelError,
  abstract,
  app,
  apps,
  bvar,
  constant,
  exprEq,
  exprToString,
  fvar,
  getAppArgs,
  getAppFn,
  instantiate1,
  lam,
  letE,
  levelEquiv,
  name as kname,
  natLit,
  param,
  pi,
  replace,
  sort,
  succ,
  visit,
  zero,
  hasParam,
  max as lmax,
  imax as limax,
  ofNat as levelOfNat,
  type ConstantInfo,
} from "@proofscript/kernel";
import type { Binder, Decl, Term } from "./lean-syntax.ts";

export class ElabError extends Error {
  override readonly name = "ElabError";
}

/** The opaque proof placeholder: `HOLE.{u} (α : Sort u) : α`. Only ever used in comparisons. */
export const HOLE = kname("_proofscript_hole");

/** Instances the elaborator may use, by class: tried in order (as Lean's instance priorities would). */
const INSTANCES: Record<string, readonly string[]> = {
  OfNat: ["instOfNatNat", "instOfNat", "UInt16.instOfNat"],
  HAdd: ["instHAdd"],
  HSub: ["instHSub"],
  HMul: ["instHMul"],
  HDiv: ["instHDiv"],
  HMod: ["instHMod"],
  HAppend: ["instHAppendOfAppend"],
  Add: ["instAddNat", "Int.instAdd"],
  Sub: ["instSubNat", "Int.instSub"],
  Mul: ["instMulNat", "Int.instMul"],
  Div: ["Nat.instDiv", "Int.instDiv"],
  Mod: ["Nat.instMod", "Int.instMod"],
  Neg: ["Int.instNegInt"],
  LT: ["instLTNat", "Int.instLTInt"],
  LE: ["instLENat", "Int.instLEInt"],
  Append: ["List.instAppend", "Array.instAppend"],
  BEq: ["instBEqOfDecidableEq"],
  DecidableEq: ["instDecidableEqNat", "instDecidableEqBool", "instDecidableEqUInt16", "Int.instDecidableEq"],
  Decidable: [
    "Nat.decLe",
    "Nat.decLt",
    "Int.decLe",
    "Int.decLt",
    "instDecidableAnd",
    "instDecidableOr",
    "instDecidableNot",
    "instDecidableEqNat",
    "instDecidableEqBool",
    "instDecidableEqUInt16",
    "Int.instDecidableEq",
  ],
  GetElem: ["Array.instGetElemNatLtSize", "List.instGetElemNatLtLength"],
};

/** Library constants the elaborator itself may introduce (besides the instances above). */
export const VOCABULARY: readonly string[] = [
  ...new Set([
    ...Object.values(INSTANCES).flat(),
    ...["Nat", "Int", "Bool", "Bool.true", "Bool.false", "Unit", "Unit.unit", "PUnit", "UInt16", "List", "Array", "Prod", "Prod.mk"],
    ...["Eq", "Ne", "Not", "And", "Or", "Iff", "Exists", "True", "False", "dite", "ite", "Decidable.decide", "autoParam"],
    ...["OfNat.ofNat", "HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HDiv.hDiv", "HMod.hMod", "HAppend.hAppend", "Neg.neg"],
    ...["LT.lt", "LE.le", "GT.gt", "GE.ge", "BEq.beq", "bne", "Bool.and", "Bool.or", "Bool.not"],
    ...["GetElem.getElem", "List.cons", "List.nil", "List.toArray", "List.length", "List.isPrefixOf", "List.isSuffixOf"],
    ...["Array.size", "Array.push", "Array.set", "Array.contains", "Array.all", "Array.any", "UInt16.toNat", "Nat.toUInt16", "Int.toNat", "Prod.fst", "Prod.snd", "Prod.rec"],
    ...["Decidable", "OfNat", "HAdd", "HSub", "HMul", "HDiv", "HMod", "HAppend", "Add", "Sub", "Mul", "Div", "Mod", "Neg", "LT", "LE"],
    ...["Append", "BEq", "DecidableEq", "GetElem", "propext", "Quot.sound", "Classical.choice", "sorryAx"],
  ]),
];

/** Names in the generated source that are notation for other constants. */
const ALIASES: Record<string, readonly string[]> = {
  true: ["Bool.true"],
  false: ["Bool.false"],
  decide: ["Decidable.decide"],
  Unit: ["Unit"],
};

interface Pending {
  readonly mvar: FVar;
  readonly type: Expr;
}

type Snapshot = [Map<number, Expr>, Map<Name, Level>];

export class Elaborator {
  readonly env: Environment;
  readonly tc: TypeChecker;
  #assign = new Map<number, Expr>();
  readonly #mvars = new Set<number>();
  #lassign = new Map<Name, Level>();
  readonly #lmvars = new Set<Name>();
  #pending: Pending[] = [];
  #numerals: FVar[] = [];
  #counter = 0;
  readonly #locals: { name: string; fv: FVar }[] = [];

  /**
   * `env` must already contain `HOLE` (see `withHole`). Exports do not preserve which binders
   * are implicit, so `binderInfos` supplies them for every constant applied by name: one
   * letter per leading binder (`d` explicit, `i` implicit, `s` strict implicit, `c` instance).
   */
  readonly binderInfos: (n: string) => string | undefined;
  constructor(env: Environment, binderInfos: (n: string) => string | undefined) {
    this.env = env;
    this.tc = new TypeChecker(env);
    this.binderInfos = binderInfos;
  }

  /** The binder kinds of `fn`'s remaining arguments, when its head is a constant. */
  #infos(fn: Expr): string | undefined {
    const h = getAppFn(fn);
    if (h.kind !== "const") return undefined;
    if (h.name === HOLE) return "d";
    const bi = this.binderInfos(nameOf(h.name));
    if (bi === undefined) throw new ElabError(`no binder information for ${nameOf(h.name)}`);
    return bi.slice(getAppArgs(fn).length);
  }

  // ---- Metavariables ------------------------------------------------------------------------

  #newMVar(type: Expr): FVar {
    const m = fvar(kname(`?m${++this.#counter}`), type);
    this.#mvars.add(m.id);
    return m;
  }
  #newLevel(): Level {
    const n = kname(`?u${++this.#counter}`);
    this.#lmvars.add(n);
    return param(n);
  }
  #isMVar(e: Expr): e is FVar {
    return e.kind === "fvar" && this.#mvars.has(e.id) && !this.#assign.has(e.id);
  }

  instLevel(l: Level): Level {
    if (!hasParam(l)) return l;
    switch (l.kind) {
      case "param": {
        const v = this.#lassign.get(l.name);
        return v === undefined ? l : this.instLevel(v);
      }
      case "succ":
        return succ(this.instLevel(l.of));
      case "max":
        return lmax(this.instLevel(l.lhs), this.instLevel(l.rhs));
      case "imax":
        return limax(this.instLevel(l.lhs), this.instLevel(l.rhs));
      default:
        return l;
    }
  }

  #assignLevel(m: Name, v: Level): boolean {
    const occurs = (x: Level): boolean =>
      x.kind === "param" ? x.name === m : x.kind === "succ" ? occurs(x.of) : x.kind === "max" || x.kind === "imax" ? occurs(x.lhs) || occurs(x.rhs) : false;
    if (occurs(v)) return false;
    this.#lassign.set(m, v);
    return true;
  }

  /** Replaces assigned metavariables (of terms and levels). */
  inst(e: Expr): Expr {
    if (!e.hasFVar && !e.hasLevelParam) return e;
    return replace(e, (s) => {
      if (!s.hasFVar && !s.hasLevelParam) return s;
      if (s.kind === "fvar") {
        const v = this.#assign.get(s.id);
        return v === undefined ? s : this.inst(v);
      }
      if (s.kind === "sort" && hasParam(s.level)) return sort(this.instLevel(s.level));
      if (s.kind === "const" && s.levels.some((l) => hasParam(l))) return constant(s.name, s.levels.map((l) => this.instLevel(l)));
      return undefined;
    });
  }

  #hasMVar(e: Expr): boolean {
    let found = false;
    visit(this.inst(e), (s) => {
      if (found) return false;
      if (s.kind === "fvar" && this.#mvars.has(s.id)) found = true;
      if (s.kind === "sort" && this.#levelHasMVar(s.level)) found = true;
      if (s.kind === "const" && s.levels.some((l) => this.#levelHasMVar(l))) found = true;
      return !found && (s.hasFVar || s.hasLevelParam);
    });
    return found;
  }
  #levelHasMVar(l: Level): boolean {
    switch (l.kind) {
      case "zero":
        return false;
      case "succ":
        return this.#levelHasMVar(l.of);
      case "max":
      case "imax":
        return this.#levelHasMVar(l.lhs) || this.#levelHasMVar(l.rhs);
      case "param":
        return this.#lmvars.has(l.name) && !this.#lassign.has(l.name);
    }
  }

  #save(): Snapshot {
    return [new Map(this.#assign), new Map(this.#lassign)];
  }
  #restore(s: Snapshot): void {
    [this.#assign, this.#lassign] = [new Map(s[0]), new Map(s[1])];
  }

  infer(e: Expr): Expr {
    try {
      return this.inst(this.tc.infer(this.inst(e)));
    } catch (err) {
      if (err instanceof KernelError) throw new ElabError(`ill-typed term: ${err.message}`);
      throw err;
    }
  }

  whnf(e: Expr): Expr {
    return this.tc.whnf(this.inst(e));
  }

  // ---- Unification --------------------------------------------------------------------------

  unifyLevel(a0: Level, b0: Level): boolean {
    const a = this.instLevel(a0);
    const b = this.instLevel(b0);
    if (a.hash === b.hash && levelEquiv(a, b)) return true;
    if (a.kind === "param" && this.#lmvars.has(a.name)) return this.#assignLevel(a.name, b);
    if (b.kind === "param" && this.#lmvars.has(b.name)) return this.#assignLevel(b.name, a);
    if (a.kind === "succ" && b.kind === "succ") return this.unifyLevel(a.of, b.of);
    // A closed level is a number: `max 1 1` against `?u + 1` solves `?u := 0`.
    const na = closedLevel(a);
    const nb = closedLevel(b);
    if (na !== undefined && nb !== undefined) return na === nb;
    if (na !== undefined && b.kind === "succ") return na > 0 && this.unifyLevel(levelOfNat(na - 1), b.of);
    if (nb !== undefined && a.kind === "succ") return nb > 0 && this.unifyLevel(a.of, levelOfNat(nb - 1));
    if (a.kind === "max" && b.kind === "max") return this.unifyLevel(a.lhs, b.lhs) && this.unifyLevel(a.rhs, b.rhs);
    if (this.#levelHasMVar(a) || this.#levelHasMVar(b)) return false;
    return levelEquiv(a, b);
  }

  unify(a0: Expr, b0: Expr): boolean {
    const a = this.inst(a0);
    const b = this.inst(b0);
    if (a === b || exprEq(a, b)) return true;
    if (this.#isMVar(a)) return this.#assignMVar(a, b);
    if (this.#isMVar(b)) return this.#assignMVar(b, a);
    const s = this.#save();
    if (this.#unifyStructural(a, b)) return true;
    this.#restore(s);
    if (!this.#hasMVar(a) && !this.#hasMVar(b)) {
      try {
        return this.tc.isDefEq(a, b);
      } catch (err) {
        if (err instanceof KernelError) return false;
        throw err;
      }
    }
    // Reduce and retry: beta/iota/projections first, then unfold a definition.
    const a1 = this.tc.whnfCore(a);
    const b1 = this.tc.whnfCore(b);
    if (!exprEq(a1, a) || !exprEq(b1, b)) return this.unify(a1, b1);
    const da = this.tc.isDelta(a);
    const db = this.tc.isDelta(b);
    // As Lean's lazy delta reduction: abbreviations first, then the greater height.
    const rank = (d: typeof da) => (d?.kind !== "definition" ? -1 : d.hints.kind === "abbrev" ? Infinity : d.hints.kind === "regular" ? d.hints.height : -1);
    const ha = rank(da);
    const hb = rank(db);
    if (da !== undefined && (db === undefined || ha >= hb)) return this.unify(this.tc.unfoldDefinition(a)!, b);
    if (db !== undefined) return this.unify(a, this.tc.unfoldDefinition(b)!);
    return false;
  }

  #unifyStructural(a: Expr, b: Expr): boolean {
    if (a.kind !== b.kind) return false;
    switch (a.kind) {
      case "sort":
        return this.unifyLevel(a.level, (b as typeof a).level);
      case "const": {
        const bb = b as typeof a;
        if (a.name !== bb.name || a.levels.length !== bb.levels.length) return false;
        return a.levels.every((l, i) => this.unifyLevel(l, bb.levels[i]!));
      }
      case "app": {
        const fa = getAppFn(a);
        const fb = getAppFn(b);
        const xa = getAppArgs(a);
        const xb = getAppArgs(b);
        if (xa.length !== xb.length) return false;
        if (!this.unify(fa, fb)) return false;
        return xa.every((x, i) => this.unify(x, xb[i]!));
      }
      case "pi":
      case "lam": {
        const bb = b as typeof a;
        if (!this.unify(a.binderType, bb.binderType)) return false;
        const x = fvar(a.binderName, this.inst(a.binderType));
        return this.unify(instantiate1(a.body, x), instantiate1(bb.body, x));
      }
      case "natLit":
        return a.value === (b as typeof a).value;
      case "proj": {
        const bb = b as typeof a;
        return a.typeName === bb.typeName && a.idx === bb.idx && this.unify(a.struct, bb.struct);
      }
      default:
        return false;
    }
  }

  #assignMVar(m: FVar, v: Expr): boolean {
    let occurs = false;
    visit(v, (s) => {
      if (s.kind === "fvar" && s.id === m.id) occurs = true;
      return !occurs && s.hasFVar;
    });
    if (occurs) return false;
    this.#assign.set(m.id, v);
    // The value must have the metavariable's type (this also fixes universe levels).
    const s = this.#save();
    if (!this.unify(m.type, this.infer(v))) {
      this.#restore(s);
      this.#assign.delete(m.id);
      return false;
    }
    return true;
  }

  // ---- Instances ----------------------------------------------------------------------------

  /** Finds an instance of class type `goal` (after instantiation), or undefined. */
  synthesize(goal0: Expr, depth = 0): Expr | undefined {
    if (depth > 8) return undefined;
    const goal = this.inst(goal0);
    const head = getAppFn(goal);
    if (head.kind !== "const") return undefined;
    const candidates = INSTANCES[nameOf(head.name)];
    if (candidates === undefined) return undefined;
    for (const cand of candidates) {
      const info = this.env.get(kname(cand));
      if (info === undefined) continue;
      const s = this.#save();
      const r = this.#tryInstance(info, goal, depth);
      if (r !== undefined) return r;
      this.#restore(s);
    }
    return undefined;
  }

  #tryInstance(info: ConstantInfo, goal: Expr, depth: number): Expr | undefined {
    let e: Expr = constant(info.name, info.levelParams.map(() => this.#newLevel()));
    let t = this.infer(e);
    const infos = this.#infos(e) ?? "";
    const subgoals: FVar[] = [];
    for (let j = 0; ; j++) {
      if (this.unify(t, goal)) break;
      const w = this.whnf(t);
      if (w.kind !== "pi") return undefined;
      const m = this.#newMVar(this.inst(w.binderType));
      if (infos[j] === "c") subgoals.push(m);
      e = app(e, m);
      t = instantiate1(w.body, m);
    }
    for (const m of subgoals) {
      if (this.#assign.has(m.id)) continue;
      const v = this.synthesize(m.type, depth + 1);
      if (v === undefined || !this.unify(m, v)) return undefined;
    }
    return this.inst(e);
  }

  #solvePending(final: boolean): void {
    for (let progress = true; progress; ) {
      progress = false;
      const rest: Pending[] = [];
      for (const p of this.#pending) {
        if (this.#assign.has(p.mvar.id)) continue;
        const ty = this.inst(p.type);
        // Wait until the class's input types are known (outParams may stay open).
        const args = getAppArgs(ty);
        if (args.length > 0 && this.#isMVar(this.inst(args[0]!)) && !final) {
          rest.push(p);
          continue;
        }
        const v = this.synthesize(ty);
        if (v === undefined) {
          if (final) throw new ElabError(`no instance for ${nameOf((getAppFn(ty) as { name: Name }).name ?? kname("?"))}`);
          rest.push(p);
          continue;
        }
        if (!this.unify(p.mvar, v)) throw new ElabError("instance does not fit");
        progress = true;
      }
      this.#pending = rest;
      if (!progress && final && this.#pending.length > 0) {
        // Lean's default instance: an unconstrained numeral is a `Nat`.
        let defaulted = false;
        for (const n of this.#numerals) {
          if (this.#isMVar(this.inst(n))) {
            this.unify(n, constant(kname("Nat"), []));
            defaulted = true;
          }
        }
        progress = defaulted;
      }
    }
  }

  /** Closes elaboration: instances, defaults, and no metavariable may remain. */
  finish(e: Expr): Expr {
    this.#solvePending(false);
    for (const n of this.#numerals) if (this.#isMVar(this.inst(n))) this.unify(n, constant(kname("Nat"), []));
    this.#solvePending(true);
    const r = this.inst(e);
    if (this.#hasMVar(r)) throw new ElabError("could not infer every implicit argument");
    if (r.hasFVar) throw new ElabError("a local variable escaped its scope");
    return r;
  }

  // ---- Names --------------------------------------------------------------------------------

  #local(n: string): FVar | undefined {
    for (let i = this.#locals.length - 1; i >= 0; i--) if (this.#locals[i]!.name === n) return this.#locals[i]!.fv;
    return undefined;
  }

  #const(n: string): Expr | undefined {
    for (const cand of ALIASES[n] ?? [n]) {
      const info = this.env.get(kname(cand));
      if (info !== undefined) return constant(info.name, info.levelParams.map(() => this.#newLevel()));
    }
    return undefined;
  }

  /** An identifier: a local or a constant, followed by any number of field accesses. */
  #resolve(n: string): { head: Expr; fields: string[] } {
    const parts = n.split(".");
    for (let k = parts.length; k >= 1; k--) {
      const prefix = parts.slice(0, k).join(".");
      const l = this.#local(prefix);
      if (l !== undefined) return { head: l, fields: parts.slice(k) };
    }
    for (let k = parts.length; k >= 1; k--) {
      const c = this.#const(parts.slice(0, k).join("."));
      if (c !== undefined) return { head: c, fields: parts.slice(k) };
    }
    throw new ElabError(`unknown name ${n}`);
  }

  #withLocal<T>(name: string, fv: FVar, k: () => T): T {
    this.#locals.push({ name, fv });
    try {
      return k();
    } finally {
      this.#locals.pop();
    }
  }

  // ---- Binders ------------------------------------------------------------------------------

  /** Elaborates binders, runs `k` in their scope, and closes the result as a Π or λ. */
  binders(bs: readonly Binder[], kind: "pi" | "lam", k: () => Expr): Expr {
    const fvs: { fv: FVar; implicit: boolean }[] = [];
    const go = (i: number): Expr => {
      if (i === bs.length) return k();
      const b = bs[i]!;
      if (b.type === undefined) throw new ElabError(`binder ${b.name} needs a type`);
      const ty = this.type(b.type);
      const fv = fvar(kname(b.name), ty);
      fvs.push({ fv, implicit: b.implicit });
      return this.#withLocal(b.name, fv, () => go(i + 1));
    };
    const body = go(0);
    return this.close(fvs, body, kind);
  }

  /** Abstracts free variables (instantiating metavariables first). */
  close(fvs: readonly { fv: FVar; implicit?: boolean }[], body: Expr, kind: "pi" | "lam"): Expr {
    // Instances may mention these variables: find them while the variables are in scope.
    this.#solvePending(false);
    let r = abstract(this.inst(body), fvs.map((x) => x.fv));
    for (let i = fvs.length - 1; i >= 0; i--) {
      const { fv, implicit } = fvs[i]!;
      const ty = abstract(this.inst(fv.type), fvs.slice(0, i).map((x) => x.fv));
      r = (kind === "pi" ? pi : lam)(fv.name, ty, r, implicit ? "implicit" : "default");
    }
    return r;
  }

  type(t: Term): Expr {
    const e = this.elab(t, undefined);
    const ty = this.whnf(this.infer(e));
    if (ty.kind !== "sort" && !this.#isMVar(ty)) throw new ElabError("expected a type");
    return e;
  }

  // ---- Terms --------------------------------------------------------------------------------

  /** Elaborates `t`, of type `expected` if given. */
  elab(t: Term, expected: Expr | undefined): Expr {
    const e = this.#elab(t, expected);
    if (expected !== undefined) this.#solvePending(false);
    if (expected !== undefined && !this.unify(this.infer(e), expected)) {
      throw new ElabError(`type mismatch in ${t.k}: ${exprToString(this.inst(this.infer(e)))} vs ${exprToString(this.inst(expected))}`);
    }
    return e;
  }

  #hole(type: Expr): Expr {
    const lv = this.#newLevel();
    const e = app(constant(HOLE, [lv]), type);
    this.unifyLevel(lv, this.#sortLevel(type));
    return e;
  }

  #sortLevel(type: Expr): Level {
    const s = this.whnf(this.infer(type));
    if (s.kind === "sort") return s.level;
    const lv = this.#newLevel();
    if (!this.unify(s, sort(lv))) throw new ElabError("expected a type");
    return lv;
  }

  #elab(t: Term, expected: Expr | undefined): Expr {
    switch (t.k) {
      case "ident": {
        const { head, fields } = this.#resolve(t.name);
        if (fields.length === 0) return this.#apply(head, [], expected);
        return this.#fields(head, fields, [], expected);
      }
      case "num": {
        const ty = expected !== undefined && !this.#isMVar(this.inst(expected)) ? this.inst(expected) : this.#newMVar(sort(succ(zero)));
        if (ty.kind === "fvar") this.#numerals.push(ty);
        return this.#numeral(t.value, ty);
      }
      case "sort":
        return sort(t.which === "Prop" ? zero : succ(zero));
      case "app": {
        const fn = t.fn;
        if (fn.k === "ident") {
          const { head, fields } = this.#resolve(fn.name);
          if (fields.length === 0) return this.#apply(head, t.args, expected);
          return this.#fields(head, fields, t.args, expected);
        }
        if (fn.k === "field") return this.#fields(this.elab(fn.e, undefined), [fn.name], t.args, expected);
        if (fn.k === "dot") return this.#apply(this.#dotCtor(fn.name, expected), t.args, expected);
        return this.#apply(this.elab(fn, undefined), t.args, expected);
      }
      case "dot":
        return this.#apply(this.#dotCtor(t.name, expected), [], expected);
      case "field":
        return this.#fields(this.elab(t.e, undefined), [t.name], [], expected);
      case "binop":
        return this.#binop(t.op, t.l, t.r, expected);
      case "unop": {
        if (t.op === "¬") return app(this.#c("Not"), this.elab(t.e, sort(zero)));
        if (t.op === "!") return app(this.#c("Bool.not"), this.elab(t.e, this.#c("Bool")));
        const x = this.elab(t.e, expected);
        return this.#classOp("Neg.neg", "Neg", this.infer(x), [x], 1);
      }
      case "ascribe": {
        const ty = this.type(t.type);
        return this.elab(t.e, ty);
      }
      case "unit":
        return this.#c("Unit.unit");
      case "tuple": {
        const ts = t.elems;
        const build = (i: number, exp: Expr | undefined): Expr => {
          if (i === ts.length - 1) return this.elab(ts[i]!, exp);
          let ea: Expr | undefined;
          let eb: Expr | undefined;
          const w = exp === undefined ? undefined : this.whnf(exp);
          if (w !== undefined && getAppFn(w).kind === "const" && nameOf((getAppFn(w) as { name: Name }).name) === "Prod") [ea, eb] = getAppArgs(w);
          const a = this.elab(ts[i]!, ea);
          const b = build(i + 1, eb);
          return this.#apply(this.#c("Prod.mk"), [], undefined, [a, b]);
        };
        return build(0, expected);
      }
      case "listLit": {
        const elemT = this.#listElem(expected);
        let r: Expr = this.#apply(this.#c("List.nil"), [], expected);
        const ty = this.infer(r);
        for (let i = t.elems.length - 1; i >= 0; i--) {
          const x = this.elab(t.elems[i]!, elemT ?? getAppArgs(this.whnf(ty))[0]);
          r = this.#apply(this.#c("List.cons"), [], ty, [x, r]);
        }
        return r;
      }
      case "arrayLit": {
        const w = expected === undefined ? undefined : this.whnf(expected);
        const elemT = w !== undefined && getAppFn(w).kind === "const" && nameOf((getAppFn(w) as { name: Name }).name) === "Array" ? getAppArgs(w)[0] : undefined;
        const listT = elemT === undefined ? undefined : this.#apply(this.#c("List"), [], undefined, [elemT]);
        const list = this.#elab({ k: "listLit", elems: t.elems }, listT);
        return this.#apply(this.#c("List.toArray"), [], expected, [list]);
      }
      case "forall":
        return this.binders(t.binders, "pi", () => this.elab(t.body, sort(zero)));
      case "exists": {
        if (t.binders.length !== 1) return this.#elab({ ...t, binders: t.binders.slice(0, 1), body: { k: "exists", binders: t.binders.slice(1), body: t.body } }, expected);
        const f = this.binders(t.binders, "lam", () => this.elab(t.body, sort(zero)));
        return this.#apply(this.#c("Exists"), [], sort(zero), [f]);
      }
      case "fun": {
        let exp = expected === undefined ? undefined : this.whnf(expected);
        const fvs: { fv: FVar }[] = [];
        const go = (i: number): Expr => {
          if (i === t.binders.length) return this.elab(t.body, exp);
          const b = t.binders[i]!;
          let ty: Expr;
          if (b.type !== undefined) ty = this.type(b.type);
          else if (exp !== undefined && exp.kind === "pi") ty = this.inst(exp.binderType);
          else ty = this.#newMVar(sort(this.#newLevel()));
          if (exp !== undefined && exp.kind === "pi" && !this.unify(ty, exp.binderType)) throw new ElabError("binder type mismatch");
          const fv = fvar(kname(b.name), ty);
          fvs.push({ fv });
          exp = exp !== undefined && exp.kind === "pi" ? this.whnf(instantiate1(exp.body, fv)) : undefined;
          return this.#withLocal(b.name, fv, () => go(i + 1));
        };
        const body = go(0);
        return this.close(fvs, body, "lam");
      }
      case "if": {
        const c = this.elab(t.cond, sort(zero));
        const resT = expected ?? this.#newMVar(sort(this.#newLevel()));
        const inst = this.#newMVar(app(this.#c("Decidable"), c));
        this.#pending.push({ mvar: inst, type: inst.type });
        const branch = (prop: Expr, body: Term): Expr => {
          const fv = fvar(kname(t.h ?? "h"), prop);
          const b = this.#withLocal(t.h ?? "", fv, () => this.elab(body, resT));
          return this.close([{ fv }], b, "lam");
        };
        const a = branch(c, t.then);
        const b = branch(app(this.#c("Not"), c), t.else);
        if (t.h === undefined) {
          const strip = (f: Expr) => (f.kind === "lam" ? f.body : f);
          return this.#apply(this.#c("ite"), [], expected, [resT, c, inst, strip(a), strip(b)], true);
        }
        return this.#apply(this.#c("dite"), [], expected, [resT, c, inst, a, b], true);
      }
      case "match":
        return this.#match(t, expected);
      case "let": {
        // `let (a, b) := v; body` is a match on a pair.
        if (t.names.length > 1) return this.#letTuple(t.names, this.elab(t.value, undefined), t.body, expected);
        const ty = t.type === undefined ? undefined : this.type(t.type);
        const v = this.elab(t.value, ty);
        const vty = ty ?? this.infer(v);
        const fv = fvar(kname(t.names[0]!), vty, v);
        const body = this.#withLocal(t.names[0]!, fv, () => this.elab(t.body, expected));
        this.#solvePending(false);
        return letE(fv.name, this.inst(vty), this.inst(v), abstract(this.inst(body), [fv]));
      }
      case "have": {
        const ty = this.elab(t.type, sort(zero));
        const v = this.#hole(ty);
        const fv = fvar(kname(t.name), ty, v);
        const body = this.#withLocal(t.name, fv, () => this.elab(t.body, expected));
        this.#solvePending(false);
        return letE(fv.name, this.inst(ty), this.inst(v), abstract(this.inst(body), [fv]));
      }
      case "by": {
        if (expected === undefined) throw new ElabError("a proof needs a known type");
        return this.#hole(expected);
      }
      case "index": {
        const coll = this.elab(t.e, undefined);
        const i = this.elab(t.i, this.#c("Nat"));
        const r = this.#apply(this.#c("GetElem.getElem"), [], expected, [coll, i], false, true);
        return r;
      }
    }
  }

  #c(...names: string[]): Expr {
    for (const n of names) {
      const c = this.#const(n);
      if (c !== undefined) return c;
    }
    throw new ElabError(`the certificate does not contain ${names.join(" / ")}`);
  }

  #numeral(v: bigint, ty: Expr): Expr {
    const inst = this.#newMVar(apps(this.#c("OfNat"), [ty, natLit(v)]));
    this.#pending.push({ mvar: inst, type: inst.type });
    return this.#apply(this.#c("OfNat.ofNat"), [], undefined, [ty, natLit(v), inst], true);
  }

  #listElem(expected: Expr | undefined): Expr | undefined {
    if (expected === undefined) return undefined;
    const w = this.whnf(expected);
    const h = getAppFn(w);
    return h.kind === "const" && nameOf(h.name) === "List" ? getAppArgs(w)[0] : undefined;
  }

  /** `@C.f α … inst args` for a class operation over a homogeneous type. */
  #classOp(opName: string, cls: string, ty: Expr, args: readonly Expr[], nTypes: number): Expr {
    const inst = this.#newMVar(apps(this.#c(cls), Array(nTypes).fill(ty)));
    this.#pending.push({ mvar: inst, type: inst.type });
    return this.#apply(this.#c(opName), [], undefined, [...Array(nTypes).fill(ty), inst, ...args], true);
  }

  #binop(op: string, l: Term, r: Term, expected: Expr | undefined): Expr {
    const arith: Record<string, [string, string]> = {
      "+": ["HAdd.hAdd", "HAdd"],
      "-": ["HSub.hSub", "HSub"],
      "*": ["HMul.hMul", "HMul"],
      "/": ["HDiv.hDiv", "HDiv"],
      "%": ["HMod.hMod", "HMod"],
      "++": ["HAppend.hAppend", "HAppend"],
    };
    const prop = sort(zero);
    const bool = () => this.#c("Bool");
    const operands = (exp: Expr | undefined): [Expr, Expr, Expr] => {
      // Lean's `binop%`: both sides share a type; numerals take it from the other side.
      const a = this.elab(l, exp);
      const ta = this.infer(a);
      const b = this.elab(r, this.#isMVar(ta) ? exp : ta);
      const tb = this.infer(b);
      if (!this.unify(ta, tb)) throw new ElabError(`operands of ${op} have different types`);
      return [a, b, this.inst(ta)];
    };
    const a2 = arith[op];
    if (a2 !== undefined) {
      const [a, b, ty] = operands(expected);
      return this.#classOp(a2[0], a2[1], ty, [a, b], 3);
    }
    switch (op) {
      case "<":
      case "≤":
      case ">":
      case "≥": {
        const [a, b, ty] = operands(undefined);
        const [fn, cls] = { "<": ["LT.lt", "LT"], "≤": ["LE.le", "LE"], ">": ["GT.gt", "LT"], "≥": ["GE.ge", "LE"] }[op]!;
        return this.#classOp(fn!, cls!, ty, [a, b], 1);
      }
      case "=":
      case "≠": {
        const [a, b, ty] = operands(undefined);
        return this.#apply(this.#c(op === "=" ? "Eq" : "Ne"), [], prop, [ty, a, b], true);
      }
      case "==":
      case "!=": {
        const [a, b, ty] = operands(undefined);
        const inst = this.#newMVar(app(this.#c("BEq"), ty));
        this.#pending.push({ mvar: inst, type: inst.type });
        return this.#apply(this.#c(op === "==" ? "BEq.beq" : "bne"), [], bool(), [ty, inst, a, b], true);
      }
      case "∧":
      case "∨":
      case "↔":
        return apps(this.#c({ "∧": "And", "∨": "Or", "↔": "Iff" }[op]!), [this.elab(l, prop), this.elab(r, prop)]);
      case "&&":
      case "||":
        return apps(op === "&&" ? this.#c("Bool.and") : this.#c("Bool.or"), [this.elab(l, bool()), this.elab(r, bool())]);
      case "→": {
        const a = this.type(l);
        const b = this.type(r);
        return pi(kname("a"), a, b);
      }
      case "×": {
        const a = this.type(l);
        const b = this.type(r);
        return this.#apply(this.#c("Prod"), [], undefined, [a, b]);
      }
    }
    throw new ElabError(`unsupported operator ${op}`);
  }

  /**
   * Applies `fn` to `args` (source terms) or `given` (already elaborated explicit arguments;
   * `allArgs`: `given` covers implicit arguments too, as with `@f`). Implicit arguments become
   * metavariables, instance arguments pending instance problems, and missing trailing
   * autoParam arguments holes. `proofLast`: the final explicit argument is a proof (`a[i]'h`).
   */
  #apply(fn: Expr, args: readonly Term[], expected: Expr | undefined, given: readonly Expr[] = [], allArgs = false, proofLast = false): Expr {
    let e = fn;
    let t = this.infer(fn);
    let ai = 0;
    let gi = 0;
    const infos = this.#infos(fn);
    const remaining = () => (ai < args.length ? 1 : 0) + (gi < given.length ? 1 : 0);
    for (let j = 0; ; j++) {
      let w = this.inst(t);
      if (w.kind !== "pi") {
        if (remaining() === 0 && !proofLast) break;
        w = this.whnf(w);
        if (w.kind !== "pi") {
          if (remaining() === 0) break;
          throw new ElabError("too many arguments");
        }
      }
      const bty = this.inst(w.binderType);
      const bi = infos === undefined ? BI[w.binderInfo] : (infos[j] ?? "d");
      let x: Expr;
      if (allArgs && gi < given.length) {
        x = given[gi++]!;
        if (!this.unify(this.infer(x), bty)) throw new ElabError("argument type mismatch");
      } else if (bi === "i" || bi === "s") {
        x = this.#newMVar(bty);
      } else if (bi === "c") {
        const m = this.#newMVar(bty);
        this.#pending.push({ mvar: m, type: bty });
        x = m;
      } else if (gi < given.length) {
        x = given[gi++]!;
        if (!this.unify(this.infer(x), bty)) throw new ElabError("argument type mismatch");
      } else if (ai < args.length) {
        x = this.elab(args[ai++]!, bty);
      } else {
        const auto = autoParamType(bty);
        if (auto !== undefined) x = this.#hole(auto);
        else if (proofLast) {
          this.#solvePending(false);
          x = this.#hole(this.inst(bty));
          proofLast = false;
        } else break;
      }
      e = app(e, x);
      t = instantiate1(w.body, x);
    }
    if (expected !== undefined && !this.unify(t, expected)) throw new ElabError(`result type mismatch: ${exprToString(this.inst(t))} vs ${exprToString(this.inst(expected))}`);
    return e;
  }

  /** Generalized field notation: `x.f args` is `T.f x args` for `x : T …`; `x.1` a projection. */
  #fields(head: Expr, fields: readonly string[], args: readonly Term[], expected: Expr | undefined): Expr {
    let e = head;
    for (let k = 0; k < fields.length; k++) {
      const f = fields[k]!;
      const last = k === fields.length - 1;
      const ty = this.whnf(this.infer(e));
      const th = getAppFn(ty);
      if (th.kind !== "const") throw new ElabError(`cannot access .${f}`);
      if (/^[0-9]+$/.test(f)) {
        const idx = Number(f) - 1;
        if (nameOf(th.name) === "Prod") {
          e = this.#apply(this.#c(idx === 0 ? "Prod.fst" : "Prod.snd"), [], undefined, [e]);
        } else throw new ElabError(`numeric projection .${f} on ${nameOf(th.name)}`);
        if (last) return this.#apply(e, args, expected);
        continue;
      }
      const fn = this.#const(`${nameOf(th.name)}.${f}`);
      if (fn === undefined) throw new ElabError(`unknown field ${nameOf(th.name)}.${f}`);
      e = this.#applyReceiver(fn, e);
      if (last) return this.#apply(e, args, expected);
    }
    return e;
  }

  /** `fn` applied up to and including its first explicit argument, `recv`. */
  #applyReceiver(fn: Expr, recv: Expr): Expr {
    let e = fn;
    let t = this.infer(fn);
    const infos = this.#infos(fn) ?? "";
    for (let j = 0; ; j++) {
      const w = this.whnf(t);
      if (w.kind !== "pi") throw new ElabError("field function takes no explicit argument");
      if ((infos[j] ?? "d") === "d") {
        if (!this.unify(this.infer(recv), w.binderType)) throw new ElabError("receiver type mismatch");
        return app(e, recv);
      }
      const m = this.#newMVar(this.inst(w.binderType));
      if (infos[j] === "c") this.#pending.push({ mvar: m, type: m.type });
      e = app(e, m);
      t = instantiate1(w.body, m);
    }
  }

  /** `.ctor` resolved against the expected type. */
  #dotCtor(n: string, expected: Expr | undefined): Expr {
    if (expected === undefined) throw new ElabError(`.${n} needs a known type`);
    const h = getAppFn(this.whnf(expected));
    if (h.kind !== "const") throw new ElabError(`.${n} needs a known type`);
    return this.#c(`${nameOf(h.name)}.${n}`);
  }

  /** `match x with | .c a b => … | _ => …` as the type's recursor (no indices, no recursion used). */
  #match(t: Term & { k: "match" }, expected: Expr | undefined): Expr {
    const discr = this.elab(t.discr, undefined);
    const dty = this.whnf(this.infer(discr));
    const ih = getAppFn(dty);
    if (ih.kind !== "const") throw new ElabError("match on a value of unknown type");
    const ind = this.env.get(ih.name);
    if (ind === undefined || ind.kind !== "inductive") throw new ElabError("match on a non-inductive type");
    if (ind.numIndices !== 0) throw new ElabError("match on an indexed family");
    const params = getAppArgs(dty).slice(0, ind.numParams);
    const resT = expected !== undefined ? this.inst(expected) : undefined;
    // The result type: from the expected type, or from the first alternative.
    let motiveBody: Expr | undefined = resT;
    const rec = this.env.get(kname(`${nameOf(ind.name)}.rec`));
    if (rec === undefined || rec.kind !== "recursor") throw new ElabError("no recursor");
    const minors: Expr[] = [];
    const recLevels = rec.levelParams.map(() => this.#newLevel());
    let recE: Expr = apps(constant(rec.name, recLevels), params);
    // Determine the motive lazily: elaborate alternatives first if needed.
    const motiveVar = this.#newMVar(pi(kname("x"), dty, sort(this.#newLevel())));
    const rw = this.whnf(this.infer(recE));
    if (rw.kind !== "pi" || !this.unify(motiveVar.type, rw.binderType)) throw new ElabError("bad recursor motive");
    recE = app(recE, motiveVar);
    let rt = this.infer(recE);
    for (const cname of ind.ctors) {
      const ctor = nameOf(cname).split(".").pop()!;
      const alt = t.alts.find((a) => a.ctor === ctor) ?? t.alts.find((a) => a.ctor === "_");
      if (alt === undefined) throw new ElabError(`match misses constructor ${ctor}`);
      const w = this.whnf(rt);
      if (w.kind !== "pi") throw new ElabError("bad recursor type");
      // The minor premise: λ fields ihs => body.
      let mt = this.whnf(w.binderType);
      const fvs: { fv: FVar }[] = [];
      const ci = this.env.get(cname);
      const nFields = ci !== undefined && ci.kind === "constructor" ? ci.numFields : 0;
      const bindNames: string[] = [];
      for (let f = 0; f < nFields; f++) bindNames.push(alt.ctor === "_" || alt.ellipsis ? "" : (alt.vars[f] ?? ""));
      if (alt.ctor !== "_" && !alt.ellipsis && alt.vars.length !== nFields) throw new ElabError(`wrong number of fields for ${ctor}`);
      while (mt.kind === "pi") {
        const fv = fvar(mt.binderName, this.inst(mt.binderType));
        fvs.push({ fv });
        mt = this.whnf(instantiate1(mt.body, fv));
      }
      const locals = fvs.slice(0, nFields).map((x, i) => ({ name: bindNames[i]!, fv: x.fv }));
      for (const l of locals) this.#locals.push(l);
      let body: Expr;
      try {
        body = this.elab(alt.body, motiveBody);
      } finally {
        for (let i = 0; i < locals.length; i++) this.#locals.pop();
      }
      if (motiveBody === undefined) motiveBody = this.infer(body);
      const minor = this.close(fvs, body, "lam");
      minors.push(minor);
      recE = app(recE, minor);
      rt = instantiate1(w.body, minor);
    }
    if (motiveBody === undefined) throw new ElabError("cannot infer the type of a match");
    const motive = lam(kname("x"), dty, motiveBody);
    if (!this.unify(motiveVar, motive)) throw new ElabError("bad match motive");
    return app(recE, discr);
  }

  /** `let (a, b, …) := v; body`: a match on (nested) pairs. */
  #letTuple(names: readonly string[], v: Expr, body: Term, expected: Expr | undefined): Expr {
    if (names.length === 1) {
      const fv = fvar(kname(names[0]!), this.infer(v), v);
      const b = this.#withLocal(names[0]!, fv, () => this.elab(body, expected));
      this.#solvePending(false);
      return letE(fv.name, this.inst(this.infer(v)), this.inst(v), abstract(this.inst(b), [fv]));
    }
    const vty = this.whnf(this.infer(v));
    const h = getAppFn(vty);
    if (h.kind !== "const" || nameOf(h.name) !== "Prod") throw new ElabError("tuple pattern on a non-pair");
    const [ta, tb] = getAppArgs(vty) as [Expr, Expr];
    const resT = expected ?? this.#newMVar(sort(this.#newLevel()));
    const a = fvar(kname(names[0]!), ta);
    const b = fvar(kname("_rest"), tb);
    const inner = this.#withLocal(names[0]!, a, () =>
      names.length === 2
        ? this.#withLocal(names[1]!, b, () => this.elab(body, resT))
        : this.#letTupleVar(b, names.slice(1), body, resT),
    );
    const minor = this.close([{ fv: a }, { fv: b }], inner, "lam");
    const motive = lam(kname("x"), vty, this.inst(resT));
    const rec = this.env.get(kname("Prod.rec"));
    if (rec === undefined) throw new ElabError("no Prod.rec");
    const lv = this.#newLevel();
    this.unifyLevel(lv, this.#sortLevel(this.inst(resT)));
    const [u, v2] = (h as { levels: readonly Level[] }).levels;
    return apps(constant(rec.name, [lv, u!, v2!]), [ta, tb, motive, minor, v]);
  }

  #letTupleVar(x: FVar, names: readonly string[], body: Term, resT: Expr): Expr {
    return this.#letTuple(names, x, body, resT);
  }

  // ---- Declarations -------------------------------------------------------------------------

  /** A theorem's statement, or a definition's type (Π binders, type). */
  signature(d: Decl & { k: "theorem" | "def" }): Expr {
    const r = this.binders(d.binders, "pi", () => (d.k === "theorem" ? this.elab(d.type, sort(zero)) : this.type(d.type)));
    return this.finish(r);
  }

  /** An inductive type's type and constructor types. */
  inductive(d: Decl & { k: "inductive" }): { type: Expr; ctors: { name: string; type: Expr }[] } {
    const type = this.finish(this.binders(d.binders, "pi", () => (d.type === undefined ? sort(succ(zero)) : this.type(d.type))));
    const ctors = d.ctors.map((c) => ({
      name: `${d.name}.${c.name}`,
      type: this.finish(this.binders([...d.binders.map((b) => ({ ...b, implicit: true })), ...c.binders], "pi", () => this.type(c.type))),
    }));
    return { type, ctors };
  }
}

export function nameOf(n: Name): string {
  const parts: string[] = [];
  let x: Name = n;
  while (x.kind !== "anonymous") {
    parts.unshift(x.kind === "str" ? x.str : String(x.num));
    x = x.prefix;
  }
  return parts.join(".");
}

function closedLevel(l: Level): number | undefined {
  switch (l.kind) {
    case "zero":
      return 0;
    case "succ": {
      const n = closedLevel(l.of);
      return n === undefined ? undefined : n + 1;
    }
    case "max":
    case "imax": {
      const x = closedLevel(l.lhs);
      const y = closedLevel(l.rhs);
      if (x === undefined || y === undefined) return undefined;
      return l.kind === "imax" && y === 0 ? 0 : Math.max(x, y);
    }
    case "param":
      return undefined;
  }
}

const BI = { default: "d", implicit: "i", strictImplicit: "s", instImplicit: "c" } as const;

/** `autoParam T stx` ↦ `T`. */
function autoParamType(t: Expr): Expr | undefined {
  const h = getAppFn(t);
  if (h.kind === "const" && nameOf(h.name) === "autoParam") return getAppArgs(t)[0];
  return undefined;
}

/** An environment with the proof placeholder `HOLE` added (a child: nothing is committed). */
export function withHole(env: Environment): Environment {
  const child = env.child();
  const u = kname("u");
  child.add({ kind: "axiom", name: HOLE, levelParams: [u], type: pi(kname("α"), sort(param(u)), bvar(0)), isUnsafe: false });
  return child;
}

