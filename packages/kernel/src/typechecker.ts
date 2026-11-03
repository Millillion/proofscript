// The type checker: type inference, weak-head normalization and definitional
// equality for Lean 4's type theory.
//
// The algorithms follow Lean 4's C++ kernel (src/kernel/type_checker.cpp,
// Apache-2.0, Copyright Microsoft Corporation), which is the de facto
// specification of the theory's decidable fragment. The code is our own.

import { type ConstantInfo, type DefinitionSafety, type Environment, KernelError, type RecursorInfo, type ReducibilityHints, isUnsafe } from "./env.ts";
import {
  type Expr,
  type FVar,
  app,
  apps,
  bvar,
  constant,
  exprEq,
  exprToString,
  fvar,
  getAppArgs,
  getAppFn,
  getAppNumArgs,
  hasLooseBVar,
  instantiate1,
  instantiateLevelParams,
  instantiateRev,
  lam,
  mkPi,
  natLit,
  proj,
  sort,
  abstract,
  instantiate,
} from "./expr.ts";
import { type Level, collectParams, imax, isAlwaysZero, levelEquiv, succ, zero } from "./level.ts";
import { type Name, name, nameToString } from "./name.ts";

// ---- Well-known names -------------------------------------------------------------

export const N = {
  Nat: name("Nat"),
  NatZero: name("Nat.zero"),
  NatSucc: name("Nat.succ"),
  String: name("String"),
  StringOfList: name("String.ofList"),
  Char: name("Char"),
  CharOfNat: name("Char.ofNat"),
  ListCons: name("List.cons"),
  ListNil: name("List.nil"),
  BoolTrue: name("Bool.true"),
  BoolFalse: name("Bool.false"),
  EagerReduce: name("eagerReduce"),
  Quot: name("Quot"),
  QuotMk: name("Quot.mk"),
  QuotLift: name("Quot.lift"),
  QuotInd: name("Quot.ind"),
};

const natBinOps = new Map<Name, (a: bigint, b: bigint) => bigint | boolean>([
  [name("Nat.add"), (a, b) => a + b],
  [name("Nat.sub"), (a, b) => (a > b ? a - b : 0n)],
  [name("Nat.mul"), (a, b) => a * b],
  [name("Nat.div"), (a, b) => (b === 0n ? 0n : a / b)],
  [name("Nat.mod"), (a, b) => (b === 0n ? a : a % b)],
  [name("Nat.gcd"), gcd],
  [name("Nat.beq"), (a, b) => a === b],
  [name("Nat.ble"), (a, b) => a <= b],
  [name("Nat.land"), (a, b) => a & b],
  [name("Nat.lor"), (a, b) => a | b],
  [name("Nat.xor"), (a, b) => a ^ b],
  [name("Nat.shiftRight"), (a, b) => a >> b],
]);
const NatPow = name("Nat.pow");
const NatShiftLeft = name("Nat.shiftLeft");

function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

/** Upper bound on the bit length of numerals the kernel computes (Lean's default is 128 MB). */
const MAX_NAT_BITS = 128n * 1024n * 1024n * 8n;
function bitLength(n: bigint): bigint {
  return BigInt(n.toString(2).length);
}

// ---- Expression-keyed maps ------------------------------------------------------------

/** A hash map keyed by expressions up to alpha-equivalence. */
export class ExprMap<V> {
  readonly #buckets = new Map<number, [Expr, V][]>();
  get(e: Expr): V | undefined {
    const b = this.#buckets.get(e.hash);
    if (b === undefined) return undefined;
    for (const [k, v] of b) if (k === e || exprEq(k, e)) return v;
    return undefined;
  }
  set(e: Expr, v: V): void {
    const b = this.#buckets.get(e.hash);
    if (b === undefined) this.#buckets.set(e.hash, [[e, v]]);
    else b.push([e, v]);
  }
}

class PairSet {
  readonly #buckets = new Map<number, [Expr, Expr][]>();
  #key(a: Expr, b: Expr): number {
    return (Math.imul(a.hash, 31) ^ b.hash) | 0;
  }
  has(a: Expr, b: Expr): boolean {
    const bucket = this.#buckets.get(this.#key(a, b));
    if (bucket === undefined) return false;
    for (const [x, y] of bucket) if (exprEq(x, a) && exprEq(y, b)) return true;
    return false;
  }
  add(a: Expr, b: Expr): void {
    const k = this.#key(a, b);
    const bucket = this.#buckets.get(k);
    if (bucket === undefined) this.#buckets.set(k, [[a, b]]);
    else bucket.push([a, b]);
  }
}

type LBool = true | false | undefined;

export interface TypeCheckerOptions {
  readonly safety?: DefinitionSafety;
  /** Level parameters in scope; `undefined` disables the check. */
  readonly levelParams?: readonly Name[];
}

export class TypeChecker {
  readonly env: Environment;
  readonly safety: DefinitionSafety;
  levelParams: readonly Name[] | undefined;
  #eagerReduce = false;

  readonly #inferCache = [new ExprMap<Expr>(), new ExprMap<Expr>()];
  readonly #whnfCoreCache = new ExprMap<Expr>();
  readonly #whnfCache = new ExprMap<Expr>();
  /** Definition bodies instantiated at specific universe levels, keyed by the constant. */
  readonly #unfoldCache = new ExprMap<Expr>();
  readonly #success = new PairSet();
  readonly #failure = new PairSet();

  constructor(env: Environment, opts: TypeCheckerOptions = {}) {
    this.env = env;
    this.safety = opts.safety ?? "safe";
    this.levelParams = opts.levelParams;
  }

  fail(msg: string): never {
    throw new KernelError(msg);
  }

  // ---- Inference -------------------------------------------------------------------

  /** Infers the type of `e`, checking that it is well typed. */
  check(e: Expr, levelParams: readonly Name[]): Expr {
    const saved = this.levelParams;
    this.levelParams = levelParams;
    try {
      return this.inferCore(e, false);
    } finally {
      this.levelParams = saved;
    }
  }

  /** Infers the type of a term already known to be well typed. */
  infer(e: Expr): Expr {
    return this.inferCore(e, true);
  }

  inferCore(e: Expr, inferOnly: boolean): Expr {
    if (e.lbr > 0) this.fail("type checker does not support loose bound variables");
    const cache = this.#inferCache[inferOnly ? 1 : 0]!;
    const hit = cache.get(e);
    if (hit !== undefined) return hit;
    let r: Expr;
    switch (e.kind) {
      case "bvar":
        this.fail("unexpected bound variable");
      case "fvar":
        r = e.type;
        break;
      case "sort":
        if (!inferOnly) this.checkLevel(e.level);
        r = sort(succ(e.level));
        break;
      case "const":
        r = this.inferConstant(e.name, e.levels, inferOnly);
        break;
      case "app":
        r = this.inferApp(e, inferOnly);
        break;
      case "lam":
        r = this.inferLambda(e, inferOnly);
        break;
      case "pi":
        r = this.inferPi(e, inferOnly);
        break;
      case "let":
        r = this.inferLet(e, inferOnly);
        break;
      case "natLit":
        if (bitLength(e.value) > MAX_NAT_BITS) this.fail("natural number literal too large");
        r = constant(N.Nat, []);
        break;
      case "strLit":
        r = constant(N.String, []);
        break;
      case "proj":
        r = this.inferProj(e, inferOnly);
        break;
    }
    cache.set(e, r);
    return r;
  }

  checkLevel(l: Level): void {
    if (this.levelParams === undefined) return;
    for (const p of collectParams(l, new Set())) {
      if (!this.levelParams.includes(p)) this.fail(`undeclared universe level parameter ${nameToString(p)}`);
    }
  }

  inferConstant(n: Name, levels: readonly Level[], inferOnly: boolean): Expr {
    const info = this.env.find(n);
    if (info.levelParams.length !== levels.length) {
      this.fail(`incorrect number of universe levels for ${nameToString(n)}: expected ${info.levelParams.length}, got ${levels.length}`);
    }
    if (!inferOnly) {
      if (isUnsafe(info) && this.safety !== "unsafe") this.fail(`invalid use of unsafe declaration ${nameToString(n)}`);
      if (info.kind === "definition" && info.safety === "partial" && this.safety === "safe") {
        this.fail(`safe declaration must not use partial declaration ${nameToString(n)}`);
      }
      for (const l of levels) this.checkLevel(l);
    }
    return instantiateLevelParams(info.type, info.levelParams, levels);
  }

  inferLambda(e0: Expr, inferOnly: boolean): Expr {
    const fvars: FVar[] = [];
    let e = e0;
    while (e.kind === "lam") {
      const d = instantiateRev(e.binderType, fvars);
      if (!inferOnly) this.ensureSort(this.inferCore(d, false));
      fvars.push(fvar(e.binderName, d));
      e = e.body;
    }
    const r = this.inferCore(instantiateRev(e, fvars), inferOnly);
    return mkPi(fvars, r);
  }

  inferPi(e0: Expr, inferOnly: boolean): Expr {
    const fvars: FVar[] = [];
    const us: Level[] = [];
    let e = e0;
    while (e.kind === "pi") {
      const d = instantiateRev(e.binderType, fvars);
      const s = this.ensureSort(this.inferCore(d, inferOnly));
      us.push(s.level);
      fvars.push(fvar(e.binderName, d));
      e = e.body;
    }
    const s = this.ensureSort(this.inferCore(instantiateRev(e, fvars), inferOnly));
    let r = s.level;
    for (let i = us.length - 1; i >= 0; i--) r = imax(us[i]!, r);
    return sort(r);
  }

  inferApp(e: Expr & { kind: "app" }, inferOnly: boolean): Expr {
    if (!inferOnly) {
      const fType = this.ensurePi(this.inferCore(e.fn, false));
      const aType = this.inferCore(e.arg, false);
      const eager = isEagerReduce(e.arg);
      const saved = this.#eagerReduce;
      if (eager) this.#eagerReduce = true;
      try {
        if (!this.isDefEq(aType, fType.binderType)) {
          this.fail(`application type mismatch: argument has type ${exprToString(aType)} but expected ${exprToString(fType.binderType)}`);
        }
      } finally {
        this.#eagerReduce = saved;
      }
      return instantiate1(fType.body, e.arg);
    }
    const args = getAppArgs(e);
    let fType = this.inferCore(getAppFn(e), true);
    let j = 0;
    for (let i = 0; i < args.length; i++) {
      if (fType.kind === "pi") {
        fType = fType.body;
      } else {
        fType = this.ensurePi(instantiateRev(fType, args.slice(j, i))).body;
        j = i;
      }
    }
    return instantiateRev(fType, args.slice(j));
  }

  inferLet(e0: Expr, inferOnly: boolean): Expr {
    const fvars: FVar[] = [];
    let e = e0;
    while (e.kind === "let") {
      const type = instantiateRev(e.binderType, fvars);
      const val = instantiateRev(e.value, fvars);
      if (!inferOnly) {
        this.ensureSort(this.inferCore(type, false));
        const valType = this.inferCore(val, false);
        if (!this.isDefEq(valType, type)) this.fail("let value type mismatch");
      }
      fvars.push(fvar(e.binderName, type, val));
      e = e.body;
    }
    const r = this.inferCore(instantiateRev(e, fvars), inferOnly);
    // Replace the let-bound variables by their values (innermost first).
    let out = abstract(r, fvars);
    for (let i = fvars.length - 1; i >= 0; i--) {
      out = instantiate(out, [abstract(fvars[i]!.value!, fvars.slice(0, i))]);
    }
    return out;
  }

  inferProj(e: Expr & { kind: "proj" }, inferOnly: boolean): Expr {
    const type = this.whnf(this.inferCore(e.struct, inferOnly));
    const args = getAppArgs(type);
    const I = getAppFn(type);
    const bad = (): never => this.fail(`invalid projection ${exprToString(e)}`);
    if (I.kind !== "const" || I.name !== e.typeName) bad();
    const info = this.env.find((I as { name: Name }).name);
    if (info.kind !== "inductive" || info.ctors.length !== 1 || args.length !== info.numParams + info.numIndices) bad();
    const ind = info as ConstantInfo & { kind: "inductive" };
    const ctor = this.env.find(ind.ctors[0]!);
    let r = instantiateLevelParams(ctor.type, ctor.levelParams, (I as { levels: readonly Level[] }).levels);
    for (let i = 0; i < ind.numParams; i++) {
      r = this.whnf(r);
      if (r.kind !== "pi") bad();
      r = instantiate1((r as { body: Expr }).body, args[i]!);
    }
    const isPropType = this.isProp(type);
    for (let i = 0; i < e.idx; i++) {
      r = this.whnf(r);
      if (r.kind !== "pi") bad();
      const p = r as Expr & { kind: "pi" };
      if (hasLooseBVar(p.body, 0)) {
        if (isPropType && !this.isProp(p.binderType)) bad();
        r = instantiate1(p.body, proj(e.typeName, i, e.struct));
      } else {
        r = p.body;
      }
    }
    r = this.whnf(r);
    if (r.kind !== "pi") bad();
    const field = (r as Expr & { kind: "pi" }).binderType;
    if (isPropType && !this.isProp(field)) bad();
    return field;
  }

  ensureSort(e: Expr): Expr & { kind: "sort" } {
    if (e.kind === "sort") return e;
    const w = this.whnf(e);
    if (w.kind === "sort") return w;
    return this.fail(`type expected, got ${exprToString(e)}`);
  }

  ensurePi(e: Expr): Expr & { kind: "pi" } {
    if (e.kind === "pi") return e;
    const w = this.whnf(e);
    if (w.kind === "pi") return w;
    return this.fail(`function expected, got ${exprToString(e)}`);
  }

  /** Whether `e` (a type) is a proposition: its sort is `Prop` for every universe assignment. */
  isProp(e: Expr): boolean {
    const s = this.ensureSort(this.infer(e));
    return isAlwaysZero(s.level);
  }

  // ---- Reduction ---------------------------------------------------------------------

  whnfCore(e: Expr, cheapRec = false, cheapProj = false): Expr {
    switch (e.kind) {
      case "bvar":
      case "sort":
      case "pi":
      case "const":
      case "lam":
      case "natLit":
      case "strLit":
        return e;
      case "fvar":
        if (e.value === undefined) return e;
        return this.whnfCore(e.value, cheapRec, cheapProj);
      default:
        break;
    }
    const cacheable = !cheapRec && !cheapProj;
    if (cacheable) {
      const hit = this.#whnfCoreCache.get(e);
      if (hit !== undefined) return hit;
    }
    let r: Expr;
    switch (e.kind) {
      case "proj": {
        const m = this.reduceProj(e, cheapRec, cheapProj);
        r = m === undefined ? e : this.whnfCore(m, cheapRec, cheapProj);
        break;
      }
      case "app": {
        const args = getAppArgs(e);
        const f0 = getAppFn(e);
        const f = this.whnfCore(f0, cheapRec, cheapProj);
        if (f.kind === "lam") {
          let body: Expr = f;
          let m = 0;
          while (body.kind === "lam" && m < args.length) {
            body = body.body;
            m++;
          }
          r = this.whnfCore(apps(instantiateRev(body, args.slice(0, m)), args.slice(m)), cheapRec, cheapProj);
        } else if (f === f0) {
          const red = this.reduceRecursor(e, cheapRec, cheapProj);
          if (red !== undefined) return this.whnfCore(red, cheapRec, cheapProj);
          return e;
        } else {
          r = this.whnfCore(apps(f, args), cheapRec, cheapProj);
        }
        break;
      }
      case "let":
        r = this.whnfCore(instantiate1(e.body, e.value), cheapRec, cheapProj);
        break;
      default:
        r = e;
    }
    if (cacheable) this.#whnfCoreCache.set(e, r);
    return r;
  }

  reduceProj(e: Expr & { kind: "proj" }, cheapRec: boolean, cheapProj: boolean): Expr | undefined {
    const c = cheapProj ? this.whnfCore(e.struct, cheapRec, cheapProj) : this.whnf(e.struct);
    return this.reduceProjCore(c, e.typeName, e.idx);
  }

  reduceProjCore(c0: Expr, sname: Name, idx: number): Expr | undefined {
    let c = c0;
    if (c.kind === "strLit") c = this.whnf(this.stringLitToConstructor(c));
    const mk = getAppFn(c);
    if (mk.kind !== "const") return undefined;
    const info = this.env.get(mk.name);
    if (info === undefined || info.kind !== "constructor" || info.induct !== sname) return undefined;
    const args = getAppArgs(c);
    return info.numParams + idx < args.length ? args[info.numParams + idx] : undefined;
  }

  whnf(e: Expr): Expr {
    switch (e.kind) {
      case "bvar":
      case "sort":
      case "pi":
      case "natLit":
      case "strLit":
        return e;
      case "fvar":
        if (e.value === undefined) return e;
        break;
      default:
        break;
    }
    const hit = this.#whnfCache.get(e);
    if (hit !== undefined) return hit;
    let t: Expr = e;
    for (;;) {
      const t1 = this.whnfCore(t);
      const v = this.reduceNat(t1);
      if (v !== undefined) {
        this.#whnfCache.set(e, v);
        return v;
      }
      const next = this.unfoldDefinition(t1);
      if (next !== undefined) {
        t = next;
        continue;
      }
      this.#whnfCache.set(e, t1);
      return t1;
    }
  }

  /** The definition (or theorem) to unfold if `e`'s head is one, with the right number of levels. */
  isDelta(e: Expr): (ConstantInfo & { kind: "definition" | "theorem" }) | undefined {
    const f = getAppFn(e);
    if (f.kind !== "const") return undefined;
    const info = this.env.get(f.name);
    if (info === undefined || (info.kind !== "definition" && info.kind !== "theorem")) return undefined;
    if (info.levelParams.length !== f.levels.length) return undefined;
    return info;
  }

  unfoldDefinition(e: Expr): Expr | undefined {
    const info = this.isDelta(e);
    if (info === undefined) return undefined;
    const f = getAppFn(e) as Expr & { kind: "const" };
    let body = f.levels.length === 0 ? info.value : this.#unfoldCache.get(f);
    if (body === undefined) {
      body = instantiateLevelParams(info.value, info.levelParams, f.levels);
      this.#unfoldCache.set(f, body);
    }
    return e === f ? body : apps(body, getAppArgs(e));
  }

  // ---- Nat and String literals --------------------------------------------------------

  natLitExt(e: Expr): bigint | undefined {
    if (e.kind === "natLit") return e.value;
    if (e.kind === "const" && e.name === N.NatZero && e.levels.length === 0) return 0n;
    return undefined;
  }

  reduceNat(e: Expr): Expr | undefined {
    const n = getAppNumArgs(e);
    if (n === 1) {
      const f = (e as Expr & { kind: "app" }).fn;
      if (f.kind === "const" && f.name === N.NatSucc && f.levels.length === 0) {
        const v = this.natLitExt(this.whnf((e as Expr & { kind: "app" }).arg));
        if (v === undefined) return undefined;
        return natLit(v + 1n);
      }
      return undefined;
    }
    if (n !== 2) return undefined;
    const f = getAppFn(e);
    if (f.kind !== "const" || f.levels.length !== 0) return undefined;
    const op = natBinOps.get(f.name);
    const isPow = f.name === NatPow;
    const isShl = f.name === NatShiftLeft;
    if (op === undefined && !isPow && !isShl) return undefined;
    const [a0, b0] = getAppArgs(e) as [Expr, Expr];
    const a = this.natLitExt(this.whnf(a0));
    if (a === undefined) return undefined;
    const b = this.natLitExt(this.whnf(b0));
    if (b === undefined) return undefined;
    let r: bigint | boolean;
    if (isPow) {
      if (b > 0xffffffffn) this.fail("Nat.pow exponent too large");
      if (a > 1n && bitLength(a) * b > MAX_NAT_BITS) this.fail("Nat.pow result too large");
      r = a ** b;
    } else if (isShl) {
      if (a !== 0n && (b > 0xffffffffn || bitLength(a) + b > MAX_NAT_BITS)) this.fail("Nat.shiftLeft result too large");
      r = a << b;
    } else {
      r = op!(a, b);
    }
    if (typeof r === "boolean") return constant(r ? N.BoolTrue : N.BoolFalse, []);
    if (bitLength(r) > MAX_NAT_BITS) this.fail("natural number too large");
    return natLit(r);
  }

  natLitToConstructor(v: bigint): Expr {
    return v === 0n ? constant(N.NatZero, []) : app(constant(N.NatSucc, []), natLit(v - 1n));
  }

  stringLitToConstructor(e: Expr & { kind: "strLit" }): Expr {
    const charType = constant(N.Char, []);
    const nil = app(constant(N.ListNil, [zero]), charType);
    const cons = app(constant(N.ListCons, [zero]), charType);
    const cps = [...e.value].map((c) => c.codePointAt(0)!);
    let r: Expr = nil;
    for (let i = cps.length - 1; i >= 0; i--) {
      r = apps(cons, [app(constant(N.CharOfNat, []), natLit(BigInt(cps[i]!))), r]);
    }
    return app(constant(N.StringOfList, []), r);
  }

  // ---- Recursors ---------------------------------------------------------------------

  reduceRecursor(e: Expr, cheapRec: boolean, cheapProj: boolean): Expr | undefined {
    if (this.env.quotInitialized) {
      const r = this.reduceQuot(e);
      if (r !== undefined) return r;
    }
    return this.reduceInductiveRec(e, cheapRec, cheapProj);
  }

  reduceQuot(e: Expr): Expr | undefined {
    const fn = getAppFn(e);
    if (fn.kind !== "const") return undefined;
    let mkPos: number;
    if (fn.name === N.QuotLift) mkPos = 5;
    else if (fn.name === N.QuotInd) mkPos = 4;
    else return undefined;
    const args = getAppArgs(e);
    if (args.length <= mkPos) return undefined;
    const mk = this.whnf(args[mkPos]!);
    const mkFn = getAppFn(mk);
    if (mkFn.kind !== "const" || mkFn.name !== N.QuotMk || getAppNumArgs(mk) !== 3) return undefined;
    const r = app(args[3]!, (mk as Expr & { kind: "app" }).arg);
    return apps(r, args.slice(mkPos + 1));
  }

  majorInduct(rec: RecursorInfo): Name | undefined {
    let t = rec.type;
    const idx = rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices;
    for (let i = 0; i < idx; i++) {
      if (t.kind !== "pi") return undefined;
      t = t.body;
    }
    if (t.kind !== "pi") return undefined;
    const f = getAppFn(t.binderType);
    return f.kind === "const" ? f.name : undefined;
  }

  reduceInductiveRec(e: Expr, cheapRec: boolean, cheapProj: boolean): Expr | undefined {
    const recFn = getAppFn(e);
    if (recFn.kind !== "const") return undefined;
    const info = this.env.get(recFn.name);
    if (info === undefined || info.kind !== "recursor") return undefined;
    const args = getAppArgs(e);
    const majorIdx = info.numParams + info.numMotives + info.numMinors + info.numIndices;
    if (majorIdx >= args.length) return undefined;
    const whnf = (x: Expr): Expr => (cheapRec ? this.whnfCore(x, cheapRec, cheapProj) : this.whnf(x));
    const majorInduct = this.majorInduct(info);
    if (majorInduct === undefined) return undefined;
    let major = args[majorIdx]!;
    if (info.k) major = this.toCtorWhenK(info, majorInduct, major, whnf);
    major = whnf(major);
    if (major.kind === "natLit") major = this.natLitToConstructor(major.value);
    else if (major.kind === "strLit") major = whnf(this.stringLitToConstructor(major));
    else major = this.toCtorWhenStructure(majorInduct, major, whnf);
    const majorFn = getAppFn(major);
    if (majorFn.kind !== "const") return undefined;
    const rule = info.rules.find((r) => r.ctor === majorFn.name);
    if (rule === undefined) return undefined;
    const majorArgs = getAppArgs(major);
    if (rule.nfields > majorArgs.length) return undefined;
    if (recFn.levels.length !== info.levelParams.length) return undefined;
    let rhs = instantiateLevelParams(rule.rhs, info.levelParams, recFn.levels);
    rhs = apps(rhs, args.slice(0, info.numParams + info.numMotives + info.numMinors));
    const nparams = majorArgs.length - rule.nfields;
    rhs = apps(rhs, majorArgs.slice(nparams));
    return apps(rhs, args.slice(majorIdx + 1));
  }

  toCtorWhenK(info: RecursorInfo, majorInduct: Name, e: Expr, whnf: (x: Expr) => Expr): Expr {
    const appType = whnf(this.infer(e));
    const I = getAppFn(appType);
    if (I.kind !== "const" || I.name !== majorInduct) return e;
    const ind = this.env.get(I.name);
    if (ind === undefined || ind.kind !== "inductive" || ind.ctors.length === 0) return e;
    const newCtor = apps(constant(ind.ctors[0]!, I.levels), getAppArgs(appType).slice(0, info.numParams));
    const newType = this.infer(newCtor);
    if (!this.isDefEq(appType, newType)) return e;
    return newCtor;
  }

  isNonRecStructure(n: Name): boolean {
    const info = this.env.get(n);
    return info !== undefined && info.kind === "inductive" && info.ctors.length === 1 && info.numIndices === 0 && !info.isRec;
  }

  isConstructorApp(e: Expr): boolean {
    const f = getAppFn(e);
    return f.kind === "const" && this.env.get(f.name)?.kind === "constructor";
  }

  toCtorWhenStructure(induct: Name, e: Expr, whnf: (x: Expr) => Expr): Expr {
    if (!this.isNonRecStructure(induct) || this.isConstructorApp(e)) return e;
    const eType = whnf(this.infer(e));
    const I = getAppFn(eType);
    if (I.kind !== "const" || I.name !== induct) return e;
    if (this.isProp(eType)) return e;
    return this.expandEtaStruct(eType, e);
  }

  expandEtaStruct(eType: Expr, e: Expr): Expr {
    const I = getAppFn(eType);
    if (I.kind !== "const") return e;
    const ind = this.env.get(I.name);
    if (ind === undefined || ind.kind !== "inductive" || ind.ctors.length === 0) return e;
    const ctor = this.env.find(ind.ctors[0]!);
    if (ctor.kind !== "constructor") return e;
    let r = apps(constant(ctor.name, I.levels), getAppArgs(eType).slice(0, ctor.numParams));
    for (let i = 0; i < ctor.numFields; i++) r = app(r, proj(I.name, i, e));
    return r;
  }

  // ---- Definitional equality -------------------------------------------------------

  isDefEq(t: Expr, s: Expr): boolean {
    const r = this.isDefEqCore(t, s);
    if (r) this.#success.add(t, s);
    return r;
  }

  isDefEqLevels(a: readonly Level[], b: readonly Level[]): boolean {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) if (!levelEquiv(a[i]!, b[i]!)) return false;
    return true;
  }

  quickIsDefEq(t: Expr, s: Expr): LBool {
    if (exprEq(t, s) || this.#success.has(t, s) || this.#success.has(s, t)) return true;
    if (t.kind === s.kind) {
      switch (t.kind) {
        case "lam":
        case "pi":
          return this.isDefEqBinding(t, s as typeof t);
        case "sort":
          return levelEquiv(t.level, (s as typeof t).level);
        case "natLit":
          return t.value === (s as typeof t).value;
        case "strLit":
          return t.value === (s as typeof t).value;
        default:
          break;
      }
    }
    return undefined;
  }

  isDefEqBinding(t0: Expr & { kind: "lam" | "pi" }, s0: Expr & { kind: "lam" | "pi" }): boolean {
    const k = t0.kind;
    const subst: Expr[] = [];
    let t: Expr = t0;
    let s: Expr = s0;
    do {
      const tb = t as Expr & { kind: "lam" | "pi" };
      const sb = s as Expr & { kind: "lam" | "pi" };
      let sType: Expr | undefined;
      if (!exprEq(tb.binderType, sb.binderType)) {
        sType = instantiateRev(sb.binderType, subst);
        const tType = instantiateRev(tb.binderType, subst);
        if (!this.isDefEq(tType, sType)) return false;
      }
      if (tb.body.lbr > 0 || sb.body.lbr > 0) {
        subst.push(fvar(sb.binderName, sType ?? instantiateRev(sb.binderType, subst)));
      } else {
        subst.push(dontCare);
      }
      t = tb.body;
      s = sb.body;
    } while (t.kind === k && s.kind === k);
    return this.isDefEq(instantiateRev(t, subst), instantiateRev(s, subst));
  }

  isDefEqArgs(t: Expr, s: Expr): boolean {
    while (t.kind === "app" && s.kind === "app") {
      if (!this.isDefEq(t.arg, s.arg)) return false;
      t = t.fn;
      s = s.fn;
    }
    return t.kind !== "app" && s.kind !== "app";
  }

  isDefEqApp(t: Expr, s: Expr): boolean {
    if (t.kind !== "app" || s.kind !== "app") return false;
    const ta = getAppArgs(t);
    const sa = getAppArgs(s);
    if (ta.length !== sa.length || !this.isDefEq(getAppFn(t), getAppFn(s))) return false;
    for (let i = 0; i < ta.length; i++) if (!this.isDefEq(ta[i]!, sa[i]!)) return false;
    return true;
  }

  isDefEqProofIrrel(t: Expr, s: Expr): LBool {
    const tType = this.infer(t);
    if (!this.isProp(tType)) return undefined;
    return this.isDefEq(tType, this.infer(s));
  }

  tryEtaExpansionCore(t: Expr, s: Expr): boolean {
    if (t.kind !== "lam" || s.kind === "lam") return false;
    const sType = this.whnf(this.infer(s));
    if (sType.kind !== "pi") return false;
    const newS = lam(sType.binderName, sType.binderType, app(s, bvar(0)), sType.binderInfo);
    return this.isDefEq(t, newS);
  }

  tryEtaStructCore(t: Expr, s: Expr): boolean {
    const f = getAppFn(s);
    if (f.kind !== "const") return false;
    const info = this.env.get(f.name);
    if (info === undefined || info.kind !== "constructor") return false;
    const sArgs = getAppArgs(s);
    if (sArgs.length !== info.numParams + info.numFields) return false;
    if (!this.isNonRecStructure(info.induct)) return false;
    if (!this.isDefEq(this.infer(t), this.infer(s))) return false;
    for (let i = info.numParams; i < sArgs.length; i++) {
      if (!this.isDefEq(proj(info.induct, i - info.numParams, t), sArgs[i]!)) return false;
    }
    return true;
  }

  isDefEqUnitLike(t: Expr, s: Expr): boolean {
    const tType = this.whnf(this.infer(t));
    const I = getAppFn(tType);
    if (I.kind !== "const" || !this.isNonRecStructure(I.name)) return false;
    const ind = this.env.find(I.name) as ConstantInfo & { kind: "inductive" };
    const ctor = this.env.find(ind.ctors[0]!);
    if (ctor.kind !== "constructor" || ctor.numFields !== 0) return false;
    return this.isDefEqCore(tType, this.infer(s));
  }

  tryStringLitExpansionCore(t: Expr, s: Expr): LBool {
    if (t.kind === "strLit" && s.kind === "app") {
      const f = s.fn;
      if (f.kind === "const" && f.name === N.StringOfList) {
        return this.isDefEqCore(this.whnf(this.stringLitToConstructor(t)), s);
      }
    }
    return undefined;
  }

  isNatZero(t: Expr): boolean {
    return (t.kind === "const" && t.name === N.NatZero && t.levels.length === 0) || (t.kind === "natLit" && t.value === 0n);
  }

  natPred(t: Expr): Expr | undefined {
    if (t.kind === "natLit") return t.value > 0n ? natLit(t.value - 1n) : undefined;
    if (t.kind === "app" && t.fn.kind === "const" && t.fn.name === N.NatSucc && t.fn.levels.length === 0) return t.arg;
    return undefined;
  }

  isDefEqOffset(t: Expr, s: Expr): LBool {
    if (this.isNatZero(t) && this.isNatZero(s)) return true;
    const pt = this.natPred(t);
    const ps = this.natPred(s);
    if (pt !== undefined && ps !== undefined) return this.isDefEqCore(pt, ps);
    return undefined;
  }

  tryUnfoldProjApp(e: Expr): Expr | undefined {
    const f = getAppFn(e);
    if (f.kind !== "proj") return undefined;
    const n = this.whnfCore(e);
    return n === e ? undefined : n;
  }

  /** One step of lazy delta reduction; updates `st`. */
  lazyDeltaReductionStep(st: { t: Expr; s: Expr }): "continue" | "unknown" | "equal" | "diff" {
    const dt = this.isDelta(st.t);
    const ds = this.isDelta(st.s);
    if (dt === undefined && ds === undefined) return "unknown";
    if (dt !== undefined && ds === undefined) {
      const sNew = this.tryUnfoldProjApp(st.s);
      if (sNew !== undefined) st.s = sNew;
      else st.t = this.whnfCore(this.unfoldDefinition(st.t)!, false, true);
    } else if (dt === undefined && ds !== undefined) {
      const tNew = this.tryUnfoldProjApp(st.t);
      if (tNew !== undefined) st.t = tNew;
      else st.s = this.whnfCore(this.unfoldDefinition(st.s)!, false, true);
    } else {
      const c = compareHints(hintsOf(dt!), hintsOf(ds!));
      if (c < 0) {
        st.t = this.whnfCore(this.unfoldDefinition(st.t)!, false, true);
      } else if (c > 0) {
        st.s = this.whnfCore(this.unfoldDefinition(st.s)!, false, true);
      } else {
        if (st.t.kind === "app" && st.s.kind === "app" && dt === ds && hintsOf(dt!).kind === "regular") {
          if (!this.#failure.has(st.t, st.s)) {
            const ft = getAppFn(st.t) as Expr & { kind: "const" };
            const fs = getAppFn(st.s) as Expr & { kind: "const" };
            if (this.isDefEqLevels(ft.levels, fs.levels) && this.isDefEqArgs(st.t, st.s)) return "equal";
            this.#failure.add(st.t, st.s);
          }
        }
        st.t = this.whnfCore(this.unfoldDefinition(st.t)!, false, true);
        st.s = this.whnfCore(this.unfoldDefinition(st.s)!, false, true);
      }
    }
    const q = this.quickIsDefEq(st.t, st.s);
    return q === true ? "equal" : q === false ? "diff" : "continue";
  }

  lazyDeltaReduction(st: { t: Expr; s: Expr }): LBool {
    for (;;) {
      const off = this.isDefEqOffset(st.t, st.s);
      if (off !== undefined) return off;
      if ((!st.t.hasFVar && !st.s.hasFVar) || this.#eagerReduce) {
        const tv = this.reduceNat(st.t);
        if (tv !== undefined) return this.isDefEqCore(tv, st.s);
        const sv = this.reduceNat(st.s);
        if (sv !== undefined) return this.isDefEqCore(st.t, sv);
      }
      switch (this.lazyDeltaReductionStep(st)) {
        case "continue":
          break;
        case "unknown":
          return undefined;
        case "equal":
          return true;
        case "diff":
          return false;
      }
    }
  }

  lazyDeltaProjReduction(t: Expr, s: Expr, sname: Name, idx: number): boolean {
    const st = { t, s };
    for (;;) {
      switch (this.lazyDeltaReductionStep(st)) {
        case "continue":
          break;
        case "equal":
          return true;
        default: {
          const pt = this.reduceProjCore(st.t, sname, idx);
          if (pt !== undefined) {
            const ps = this.reduceProjCore(st.s, sname, idx);
            if (ps !== undefined) return this.isDefEqCore(pt, ps);
          }
          return this.isDefEqCore(st.t, st.s);
        }
      }
    }
  }

  isDefEqCore(t: Expr, s: Expr): boolean {
    const q = this.quickIsDefEq(t, s);
    if (q !== undefined) return q;

    if ((!t.hasFVar || this.#eagerReduce) && s.kind === "const" && s.name === N.BoolTrue) {
      const w = this.whnf(t);
      if (w.kind === "const" && w.name === N.BoolTrue) return true;
    }

    let tn = this.whnfCore(t, false, true);
    let sn = this.whnfCore(s, false, true);
    if (tn !== t || sn !== s) {
      const q2 = this.quickIsDefEq(tn, sn);
      if (q2 !== undefined) return q2;
    }

    const pi = this.isDefEqProofIrrel(tn, sn);
    if (pi !== undefined) return pi;

    const st = { t: tn, s: sn };
    const ld = this.lazyDeltaReduction(st);
    if (ld !== undefined) return ld;
    tn = st.t;
    sn = st.s;

    if (tn.kind === "const" && sn.kind === "const" && tn.name === sn.name && this.isDefEqLevels(tn.levels, sn.levels)) return true;
    if (tn.kind === "fvar" && sn.kind === "fvar" && tn.id === sn.id) return true;
    if (tn.kind === "proj" && sn.kind === "proj" && tn.typeName === sn.typeName && tn.idx === sn.idx) {
      if (this.lazyDeltaProjReduction(tn.struct, sn.struct, tn.typeName, tn.idx)) return true;
    }

    const tnn = this.whnfCore(tn);
    const snn = this.whnfCore(sn);
    if (tnn !== tn || snn !== sn) return this.isDefEqCore(tnn, snn);

    if (this.isDefEqApp(tn, sn)) return true;
    if (this.tryEtaExpansionCore(tn, sn) || this.tryEtaExpansionCore(sn, tn)) return true;
    if (this.tryEtaStructCore(tn, sn) || this.tryEtaStructCore(sn, tn)) return true;
    const str = this.tryStringLitExpansionCore(tn, sn) ?? this.tryStringLitExpansionCore(sn, tn);
    if (str !== undefined) return str;
    if (this.isDefEqUnitLike(tn, sn)) return true;
    return false;
  }
}

// ---- Helpers -------------------------------------------------------------------------

const dontCare: Expr = constant(name("dontcare"), []);

function isEagerReduce(e: Expr): boolean {
  const f = getAppFn(e);
  return f.kind === "const" && f.name === N.EagerReduce && getAppNumArgs(e) === 2;
}

function hintsOf(c: ConstantInfo): ReducibilityHints {
  return c.kind === "definition" ? c.hints : { kind: "opaque" };
}

/** < 0: unfold the first; > 0: unfold the second; 0: unfold both. */
function compareHints(h1: ReducibilityHints, h2: ReducibilityHints): number {
  if (h1.kind === h2.kind) {
    if (h1.kind === "regular" && h2.kind === "regular") {
      if (h1.height === h2.height) return 0;
      return h1.height > h2.height ? -1 : 1;
    }
    return 0;
  }
  if (h1.kind === "opaque") return 1;
  if (h2.kind === "opaque") return -1;
  if (h1.kind === "abbrev") return -1;
  if (h2.kind === "abbrev") return 1;
  return 0;
}
