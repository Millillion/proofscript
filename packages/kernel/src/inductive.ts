// Inductive declarations: well-formedness checks, recursor generation, and
// elimination of nested inductive types.
//
// Follows Lean 4's src/kernel/inductive.cpp (Apache-2.0, Copyright Microsoft
// Corporation). The recursors are always generated here; recursors supplied by
// an export file are only compared against ours, never trusted.

import {
  type ConstructorInfo,
  type Environment,
  type InductiveInfo,
  KernelError,
  type RecursorInfo,
  type RecursorRule,
} from "./env.ts";
import {
  type Expr,
  type FVar,
  abstract,
  apps,
  constant,
  consumeTypeAnnotations,
  exprAny,
  exprEq,
  exprToString,
  fvar,
  getAppArgs,
  getAppFn,
  instantiate1,
  instantiateLevelParams,
  instantiateRev,
  mkLambda,
  mkPi,
  replace,
  sort,
  visit,
} from "./expr.ts";
import { type Level, isAlwaysZero, isNeverZero, levelEquiv, geq, param, zero } from "./level.ts";
import { type Name, anonymous, appendAfter, isPrefixOf, name, nameToString, numName, replacePrefix, strName } from "./name.ts";
import { TypeChecker } from "./typechecker.ts";

export interface IndCtor {
  readonly name: Name;
  readonly type: Expr;
}
export interface IndType {
  readonly name: Name;
  readonly type: Expr;
  readonly ctors: readonly IndCtor[];
}
export interface InductiveDecl {
  readonly levelParams: readonly Name[];
  readonly numParams: number;
  readonly types: readonly IndType[];
  readonly isUnsafe: boolean;
}

export interface InductiveResult {
  readonly types: InductiveInfo[];
  readonly ctors: ConstructorInfo[];
  readonly recs: RecursorInfo[];
}

const NESTED = name("_nested");

const fail = (msg: string): never => {
  throw new KernelError(msg);
};

function recName(I: Name): Name {
  return strName(I, "rec");
}

function checkDuplicatedUnivParams(ls: readonly Name[]): void {
  if (new Set(ls).size !== ls.length) fail("duplicate universe level parameter");
}

function checkNoFVar(n: Name, e: Expr): void {
  if (e.hasFVar) fail(`declaration ${nameToString(n)} contains free variables`);
  if (e.lbr > 0) fail(`declaration ${nameToString(n)} contains loose bound variables`);
}

// ---- The core algorithm (no nested occurrences) ---------------------------------------

class AddInductive {
  readonly env: Environment;
  readonly lparams: readonly Name[];
  readonly nparams: number;
  readonly isUnsafe: boolean;
  readonly indTypes: readonly IndType[];
  readonly nnested: number;
  nindices: number[] = [];
  resultLevel: Level = zero;
  levels: Level[] = [];
  isNotZero = false;
  params: FVar[] = [];
  indConsts: Expr[] = [];
  elimLevel: Level = zero;
  kTarget = false;
  recInfos: { C: FVar; minors: FVar[]; indices: FVar[]; major: FVar }[] = [];
  readonly out: InductiveResult = { types: [], ctors: [], recs: [] };

  constructor(env: Environment, decl: InductiveDecl, nnested: number) {
    this.env = env;
    this.lparams = decl.levelParams;
    this.nparams = decl.numParams;
    this.isUnsafe = decl.isUnsafe;
    this.indTypes = decl.types;
    this.nnested = nnested;
  }

  tc(): TypeChecker {
    return new TypeChecker(this.env, { safety: this.isUnsafe ? "unsafe" : "safe" });
  }
  whnf(e: Expr): Expr {
    return this.tc().whnf(e);
  }
  infer(e: Expr): Expr {
    return this.tc().infer(e);
  }
  isDefEq(a: Expr, b: Expr): boolean {
    return this.tc().isDefEq(a, b);
  }
  localFor(t: Expr): FVar {
    if (t.kind !== "pi") return fail("expected a binder");
    return fvar(t.binderName, consumeTypeAnnotations(t.binderType));
  }
  checkName(n: Name): void {
    if (this.env.has(n)) fail(`${nameToString(n)} has already been declared`);
  }

  checkInductiveTypes(): void {
    this.levels = this.lparams.map(param);
    let first = true;
    for (const it of this.indTypes) {
      let type = it.type;
      this.checkName(it.name);
      this.checkName(recName(it.name));
      checkNoFVar(it.name, type);
      this.tc().check(type, this.lparams);
      let nidx = 0;
      let i = 0;
      type = this.whnf(type);
      while (type.kind === "pi") {
        if (i < this.nparams) {
          if (first) {
            const p = this.localFor(type);
            this.params.push(p);
            type = instantiate1(type.body, p);
          } else {
            if (!this.isDefEq(type.binderType, this.params[i]!.type)) fail("parameters of all inductive datatypes must match");
            type = instantiate1(type.body, this.params[i]!);
          }
          i++;
        } else {
          const l = this.localFor(type);
          type = instantiate1(type.body, l);
          nidx++;
        }
        type = this.whnf(type);
      }
      if (i !== this.nparams) fail("number of parameters mismatch in inductive datatype declaration");
      const s = this.tc().ensureSort(type);
      if (first) {
        this.resultLevel = s.level;
        this.isNotZero = isNeverZero(s.level);
      } else if (!levelEquiv(s.level, this.resultLevel)) {
        fail("mutually inductive types must live in the same universe");
      }
      this.nindices.push(nidx);
      this.indConsts.push(constant(it.name, this.levels));
      first = false;
    }
  }

  isIndOcc(e: Expr): boolean {
    return e.kind === "const" && this.indConsts.some((c) => (c as Expr & { kind: "const" }).name === e.name);
  }
  hasIndOcc(t: Expr): boolean {
    return exprAny(t, (e) => this.isIndOcc(e));
  }

  isRec(): boolean {
    for (const it of this.indTypes) {
      for (const c of it.ctors) {
        let t = c.type;
        while (t.kind === "pi") {
          if (this.hasIndOcc(t.binderType)) return true;
          t = t.body;
        }
      }
    }
    return false;
  }

  isReflexive(): boolean {
    for (const it of this.indTypes) {
      for (const c of it.ctors) {
        let t = c.type;
        while (t.kind === "pi") {
          if (t.binderType.kind === "pi" && this.hasIndOcc(t.binderType)) return true;
          const l = this.localFor(t);
          t = instantiate1(t.body, l);
        }
      }
    }
    return false;
  }

  declareInductiveTypes(): void {
    const rec = this.isRec();
    const reflexive = this.isReflexive();
    const all = this.indTypes.map((t) => t.name);
    this.indTypes.forEach((it, idx) => {
      const info: InductiveInfo = {
        kind: "inductive",
        name: it.name,
        levelParams: this.lparams,
        type: it.type,
        numParams: this.nparams,
        numIndices: this.nindices[idx]!,
        all,
        ctors: it.ctors.map((c) => c.name),
        numNested: this.nnested,
        isRec: rec,
        isUnsafe: this.isUnsafe,
        isReflexive: reflexive,
      };
      this.checkName(it.name);
      this.env.add(info);
      this.out.types.push(info);
    });
  }

  isValidIndAppAt(t: Expr, i: number): boolean {
    const I = getAppFn(t);
    const args = getAppArgs(t);
    if (!exprEq(I, this.indConsts[i]!) || args.length !== this.nparams + this.nindices[i]!) return false;
    for (let k = 0; k < this.nparams; k++) if (!exprEq(this.params[k]!, args[k]!)) return false;
    for (let k = this.nparams; k < args.length; k++) if (this.hasIndOcc(args[k]!)) return false;
    return true;
  }
  isValidIndApp(t: Expr): number | undefined {
    for (let i = 0; i < this.indTypes.length; i++) if (this.isValidIndAppAt(t, i)) return i;
    return undefined;
  }

  isRecArgument(t0: Expr): number | undefined {
    let t = this.whnf(t0);
    while (t.kind === "pi") {
      const l = this.localFor(t);
      t = this.whnf(instantiate1(t.body, l));
    }
    return this.isValidIndApp(t);
  }

  checkPositivity(t0: Expr, ctor: Name, argIdx: number): void {
    const t = this.whnf(t0);
    if (!this.hasIndOcc(t)) return;
    if (t.kind === "pi") {
      if (this.hasIndOcc(t.binderType)) fail(`arg #${argIdx + 1} of ${nameToString(ctor)} has a non positive occurrence of the datatypes being declared`);
      const l = this.localFor(t);
      this.checkPositivity(instantiate1(t.body, l), ctor, argIdx);
    } else if (this.isValidIndApp(t) !== undefined) {
      // recursive argument
    } else {
      fail(`arg #${argIdx + 1} of ${nameToString(ctor)} contains a non valid occurrence of the datatypes being declared`);
    }
  }

  checkConstructors(): void {
    this.indTypes.forEach((it, idx) => {
      const found = new Set<Name>();
      for (const c of it.ctors) {
        if (found.has(c.name)) fail(`duplicate constructor name ${nameToString(c.name)}`);
        found.add(c.name);
        let t = c.type;
        this.checkName(c.name);
        checkNoFVar(c.name, t);
        this.tc().check(t, this.lparams);
        let i = 0;
        while (t.kind === "pi") {
          if (i < this.nparams) {
            if (!this.isDefEq(t.binderType, this.params[i]!.type)) {
              fail(`arg #${i + 1} of ${nameToString(c.name)} does not match inductive datatype parameters`);
            }
            t = instantiate1(t.body, this.params[i]!);
          } else {
            const s = this.tc().ensureSort(this.infer(t.binderType));
            if (!(geq(this.resultLevel, s.level) || isAlwaysZero(this.resultLevel))) {
              fail(`universe level of type of arg #${i + 1} of ${nameToString(c.name)} is too big for the corresponding inductive datatype`);
            }
            if (!this.isUnsafe) this.checkPositivity(t.binderType, c.name, i);
            const l = this.localFor(t);
            t = instantiate1(t.body, l);
          }
          i++;
        }
        if (!this.isValidIndAppAt(t, idx)) fail(`invalid return type for ${nameToString(c.name)}`);
      }
    });
  }

  declareConstructors(): void {
    this.indTypes.forEach((it) => {
      it.ctors.forEach((c, cidx) => {
        let arity = 0;
        for (let t = c.type; t.kind === "pi"; t = t.body) arity++;
        const info: ConstructorInfo = {
          kind: "constructor",
          name: c.name,
          levelParams: this.lparams,
          type: c.type,
          induct: it.name,
          cidx,
          numParams: this.nparams,
          numFields: arity - this.nparams,
          isUnsafe: this.isUnsafe,
        };
        this.checkName(c.name);
        this.env.add(info);
        this.out.ctors.push(info);
      });
    });
  }

  elimOnlyAtUniverseZero(): boolean {
    if (this.isNotZero) return false;
    if (this.indTypes.length > 1) return true;
    const ctors = this.indTypes[0]!.ctors;
    if (ctors.length > 1) return true;
    if (ctors.length === 0) return false;
    let type = ctors[0]!.type;
    let i = 0;
    const toCheck: FVar[] = [];
    while (type.kind === "pi") {
      const fv = this.localFor(type);
      if (i >= this.nparams) {
        const s = this.tc().ensureSort(this.infer(type.binderType));
        if (!isAlwaysZero(s.level)) toCheck.push(fv);
      }
      type = instantiate1(type.body, fv);
      i++;
    }
    const resultArgs = getAppArgs(type);
    for (const arg of toCheck) if (!resultArgs.some((a) => exprEq(a, arg))) return true;
    return false;
  }

  initElimLevel(): void {
    if (this.elimOnlyAtUniverseZero()) {
      this.elimLevel = zero;
    } else {
      let u = name("u");
      let i = 1;
      while (this.lparams.includes(u)) {
        u = appendAfter(name("u"), `_${i}`);
        i++;
      }
      this.elimLevel = param(u);
    }
  }

  initKTarget(): void {
    this.kTarget = this.indTypes.length === 1 && isAlwaysZero(this.resultLevel) && this.indTypes[0]!.ctors.length === 1;
    if (!this.kTarget) return;
    let it = this.indTypes[0]!.ctors[0]!.type;
    let i = 0;
    while (it.kind === "pi") {
      if (i < this.nparams) it = it.body;
      else {
        this.kTarget = false;
        break;
      }
      i++;
    }
  }

  getIIndices(t: Expr): { idx: number; indices: Expr[] } {
    const idx = this.isValidIndApp(t);
    if (idx === undefined) return fail(`internal error: expected an inductive application, got ${exprToString(t)}`);
    return { idx, indices: getAppArgs(t).slice(this.nparams) };
  }

  /** Splits a constructor type into its fields (after the parameters). */
  ctorFields(c: IndCtor): { fields: FVar[]; recFields: FVar[]; result: Expr } {
    let t = c.type;
    let i = 0;
    const fields: FVar[] = [];
    const recFields: FVar[] = [];
    while (t.kind === "pi") {
      if (i < this.nparams) {
        t = instantiate1(t.body, this.params[i]!);
      } else {
        const l = this.localFor(t);
        fields.push(l);
        if (this.isRecArgument(t.binderType) !== undefined) recFields.push(l);
        t = instantiate1(t.body, l);
      }
      i++;
    }
    return { fields, recFields, result: t };
  }

  mkRecInfos(): void {
    this.indTypes.forEach((it, dIdx) => {
      let t = this.whnf(it.type);
      let i = 0;
      const indices: FVar[] = [];
      while (t.kind === "pi") {
        if (i < this.nparams) {
          t = instantiate1(t.body, this.params[i]!);
        } else {
          const idx = this.localFor(t);
          indices.push(idx);
          t = instantiate1(t.body, idx);
        }
        i++;
        t = this.whnf(t);
      }
      const major = fvar(name("t"), apps(apps(this.indConsts[dIdx]!, this.params), indices));
      let CTy: Expr = sort(this.elimLevel);
      CTy = mkPi([major], CTy);
      CTy = mkPi(indices, CTy);
      const Cname = this.indTypes.length > 1 ? appendAfter(name("motive"), `_${dIdx + 1}`) : name("motive");
      this.recInfos.push({ C: fvar(Cname, CTy), minors: [], indices, major });
    });
    this.indTypes.forEach((it, dIdx) => {
      for (const c of it.ctors) {
        const { fields, recFields, result } = this.ctorFields(c);
        const { idx: itIdx, indices } = this.getIIndices(result);
        let Capp = apps(this.recInfos[itIdx]!.C, indices);
        const introApp = apps(apps(constant(c.name, this.levels), this.params), fields);
        Capp = apps(Capp, [introApp]);
        const v: FVar[] = [];
        for (const ui of recFields) {
          let uiTy = this.whnf(this.infer(ui));
          const xs: FVar[] = [];
          while (uiTy.kind === "pi") {
            const x = this.localFor(uiTy);
            xs.push(x);
            uiTy = this.whnf(instantiate1(uiTy.body, x));
          }
          const r = this.getIIndices(uiTy);
          const CappI = apps(apps(this.recInfos[r.idx]!.C, r.indices), [apps(ui, xs)]);
          v.push(fvar(appendAfter(ui.name, "_ih"), mkPi(xs, CappI)));
        }
        const minorTy = mkPi(fields, mkPi(v, Capp));
        const minorName = replacePrefix(c.name, it.name, anonymous);
        this.recInfos[dIdx]!.minors.push(fvar(minorName, minorTy));
      }
    });
  }

  recLevels(): Level[] {
    return this.elimLevel.kind === "param" ? [this.elimLevel, ...this.levels] : this.levels;
  }
  recLParams(): Name[] {
    return this.elimLevel.kind === "param" ? [this.elimLevel.name, ...this.lparams] : [...this.lparams];
  }

  mkRecRules(dIdx: number, Cs: FVar[], minors: FVar[], minorIdx: { i: number }): RecursorRule[] {
    const lvls = this.recLevels();
    const rules: RecursorRule[] = [];
    for (const c of this.indTypes[dIdx]!.ctors) {
      const { fields, recFields } = this.ctorFields(c);
      const v: Expr[] = [];
      for (const ui of recFields) {
        let uiTy = this.whnf(this.infer(ui));
        const xs: FVar[] = [];
        while (uiTy.kind === "pi") {
          const x = this.localFor(uiTy);
          xs.push(x);
          uiTy = this.whnf(instantiate1(uiTy.body, x));
        }
        const r = this.getIIndices(uiTy);
        const recApp = apps(constant(recName(this.indTypes[r.idx]!.name), lvls), [...this.params, ...Cs, ...minors, ...r.indices, apps(ui, xs)]);
        v.push(mkLambda(xs, recApp));
      }
      const eApp = apps(apps(minors[minorIdx.i]!, fields), v);
      const rhs = mkLambda(this.params, mkLambda(Cs, mkLambda(minors, mkLambda(fields, eApp))));
      rules.push({ ctor: c.name, nfields: fields.length, rhs });
      minorIdx.i++;
    }
    return rules;
  }

  declareRecursors(): void {
    const Cs = this.recInfos.map((r) => r.C);
    const minors = this.recInfos.flatMap((r) => r.minors);
    const all = this.indTypes.map((t) => t.name);
    const minorIdx = { i: 0 };
    this.indTypes.forEach((it, dIdx) => {
      const info = this.recInfos[dIdx]!;
      const Capp = apps(apps(info.C, info.indices), [info.major]);
      let recTy = mkPi([info.major], Capp);
      recTy = mkPi(info.indices, recTy);
      recTy = mkPi(minors, recTy);
      recTy = mkPi(Cs, recTy);
      recTy = mkPi(this.params, recTy);
      const rules = this.mkRecRules(dIdx, Cs, minors, minorIdx);
      const rn = recName(it.name);
      this.checkName(rn);
      const rec: RecursorInfo = {
        kind: "recursor",
        name: rn,
        levelParams: this.recLParams(),
        type: recTy,
        all,
        numParams: this.nparams,
        numIndices: this.nindices[dIdx]!,
        numMotives: Cs.length,
        numMinors: minors.length,
        rules,
        k: this.kTarget,
        isUnsafe: this.isUnsafe,
      };
      this.env.add(rec);
      this.out.recs.push(rec);
    });
  }

  /** Defensive re-check: recursor types are well typed and computation rules preserve types. */
  checkRecursors(): void {
    const Cs = this.recInfos.map((r) => r.C);
    const minors = this.recInfos.flatMap((r) => r.minors);
    this.indTypes.forEach((it) => {
      const rn = recName(it.name);
      const rec = this.env.find(rn);
      this.tc().check(rec.type, this.recLParams());
      const recPre = apps(constant(rn, this.recLevels()), [...this.params, ...Cs, ...minors]);
      for (const c of it.ctors) {
        const { fields, result } = this.ctorFields(c);
        const { indices } = this.getIIndices(result);
        const intro = apps(apps(constant(c.name, this.levels), this.params), fields);
        const lhs = apps(recPre, [...indices, intro]);
        const tc = this.tc();
        const expected = tc.infer(lhs);
        const reduct = tc.whnf(lhs);
        const actual = tc.infer(reduct);
        if (!tc.isDefEq(actual, expected)) fail(`generated recursor computation rule for ${nameToString(c.name)} is not type-preserving`);
      }
    });
  }

  run(): InductiveResult {
    checkDuplicatedUnivParams(this.lparams);
    this.checkInductiveTypes();
    this.declareInductiveTypes();
    this.checkConstructors();
    this.declareConstructors();
    this.initElimLevel();
    this.initKTarget();
    this.mkRecInfos();
    this.declareRecursors();
    this.checkRecursors();
    return this.out;
  }
}

// ---- Nested inductive types ------------------------------------------------------------

class ElimNested {
  readonly env: Environment;
  readonly decl: InductiveDecl;
  readonly lvls: Level[];
  params: FVar[] = [];
  nestedAux: [Expr, Name][] = [];
  newTypes: IndType[] = [];
  nextIdx = 1;

  constructor(env: Environment, decl: InductiveDecl) {
    this.env = env;
    this.decl = decl;
    this.lvls = decl.levelParams.map(param);
  }

  mkUniqueName(n: Name): Name {
    for (;;) {
      const r = appendAfter(n, `_${this.nextIdx}`);
      this.nextIdx++;
      if (!this.env.has(r)) return r;
    }
  }

  replaceParams(e: Expr, As: FVar[]): Expr {
    return instantiateRev(abstract(e, As), this.params);
  }

  isNestedIndApp(e: Expr): (InductiveInfo & { kind: "inductive" }) | undefined {
    if (e.kind !== "app") return undefined;
    const fn = getAppFn(e);
    if (fn.kind !== "const") return undefined;
    const info = this.env.get(fn.name);
    if (info === undefined || info.kind !== "inductive") return undefined;
    const args = getAppArgs(e);
    if (info.numParams > args.length) return undefined;
    let isNested = false;
    let loose = false;
    for (let i = 0; i < info.numParams; i++) {
      if (args[i]!.lbr > 0) loose = true;
      if (exprAny(args[i]!, (t) => t.kind === "const" && this.newTypes.some((it) => it.name === t.name))) isNested = true;
    }
    if (!isNested) return undefined;
    if (loose) fail(`invalid nested inductive datatype ${nameToString(fn.name)}, nested inductive datatypes parameters cannot contain local variables`);
    return info;
  }

  instantiatePiParams(e: Expr, n: number, ps: readonly Expr[]): Expr {
    for (let i = 0; i < n; i++) {
      if (e.kind !== "pi") fail("invalid nested inductive datatype, ill-formed declaration");
      e = (e as Expr & { kind: "pi" }).body;
    }
    return instantiateRev(e, ps.slice(0, n));
  }

  replaceIfNested(As: FVar[], e: Expr): Expr | undefined {
    const Ival = this.isNestedIndApp(e);
    if (Ival === undefined) return undefined;
    const args = getAppArgs(e);
    const fn = getAppFn(e) as Expr & { kind: "const" };
    const Inparams = Ival.numParams;
    const IAs = apps(fn, args.slice(0, Inparams));
    const Iparams = this.replaceParams(IAs, As);
    const hit = this.nestedAux.find(([e2]) => exprEq(e2, Iparams));
    if (hit !== undefined) {
      return apps(apps(constant(hit[1], this.lvls), As), args.slice(Inparams));
    }
    let result: Expr | undefined;
    for (const Jname of Ival.all) {
      const Jinfo = this.env.find(Jname);
      if (Jinfo.kind !== "inductive") fail("ill-formed nested inductive");
      const J = constant(Jname, fn.levels);
      const JAs = apps(J, args.slice(0, Inparams));
      const auxJname = this.mkUniqueName(appendName(NESTED, Jname));
      let auxJtype = instantiateLevelParams(Jinfo.type, Jinfo.levelParams, fn.levels);
      auxJtype = this.instantiatePiParams(auxJtype, Inparams, args);
      auxJtype = mkPi(As, auxJtype);
      this.nestedAux.push([this.replaceParams(JAs, As), auxJname]);
      if (Jname === fn.name) result = apps(apps(constant(auxJname, this.lvls), As), args.slice(Inparams));
      const ctors: IndCtor[] = [];
      for (const cn of (Jinfo as InductiveInfo).ctors) {
        const cinfo = this.env.find(cn);
        const auxCname = replacePrefix(cn, Jname, auxJname);
        let ct = instantiateLevelParams(cinfo.type, cinfo.levelParams, fn.levels);
        ct = this.instantiatePiParams(ct, Inparams, args);
        ct = mkPi(As, ct);
        ctors.push({ name: auxCname, type: ct });
      }
      this.newTypes.push({ name: auxJname, type: auxJtype, ctors });
    }
    return result ?? fail("internal error in nested inductive elimination");
  }

  replaceAllNested(As: FVar[], e: Expr): Expr {
    return replace(e, (s) => this.replaceIfNested(As, s));
  }

  getParams(type: Expr, n: number): { rest: Expr; ps: FVar[] } {
    const ps: FVar[] = [];
    for (let i = 0; i < n; i++) {
      if (type.kind !== "pi") fail("invalid inductive datatype declaration, incorrect number of parameters");
      const p = type as Expr & { kind: "pi" };
      const x = fvar(p.binderName, instantiateRev(p.binderType, ps));
      ps.push(x);
      type = p.body;
    }
    return { rest: instantiateRev(type, ps), ps };
  }

  run(): InductiveDecl {
    this.newTypes = [...this.decl.types];
    if (this.newTypes.length === 0) fail("invalid empty (mutual) inductive datatype declaration");
    this.params = this.getParams(this.newTypes[0]!.type, this.decl.numParams).ps;
    for (let q = 0; q < this.newTypes.length; q++) {
      const it = this.newTypes[q]!;
      const ctors: IndCtor[] = [];
      for (const c of it.ctors) {
        const { rest, ps: As } = this.getParams(c.type, this.decl.numParams);
        const nt = this.replaceAllNested(As, rest);
        ctors.push({ name: c.name, type: mkPi(As, nt) });
      }
      this.newTypes[q] = { name: it.name, type: it.type, ctors };
    }
    return { levelParams: this.decl.levelParams, numParams: this.decl.numParams, types: this.newTypes, isUnsafe: this.decl.isUnsafe };
  }

  // Restoration of nested occurrences in the auxiliary declaration's output.

  aux2nested(n: Name): Expr | undefined {
    return this.nestedAux.find(([, aux]) => aux === n)?.[0];
  }

  nestedIfAuxCtor(auxEnv: Environment, c: Name): [Expr, Name] | undefined {
    const info = auxEnv.get(c);
    if (info === undefined || info.kind !== "constructor") return undefined;
    const nested = this.aux2nested(info.induct);
    return nested === undefined ? undefined : [nested, info.induct];
  }

  restoreCtorName(auxEnv: Environment, c: Name): Name {
    const p = this.nestedIfAuxCtor(auxEnv, c);
    if (p === undefined) return fail(`failed to restore nested inductive types: ${nameToString(c)}`);
    const I = getAppFn(p[0]);
    if (I.kind !== "const") return fail("failed to restore nested inductive types");
    return replacePrefix(c, p[1], I.name);
  }

  restoreNested(e0: Expr, auxEnv: Environment, auxRecMap: Map<Name, Name> = new Map()): Expr {
    let e = e0;
    const As: FVar[] = [];
    const isPi = e.kind === "pi";
    for (let i = 0; i < this.params.length; i++) {
      if (e.kind !== "pi" && e.kind !== "lam") fail("failed to restore nested inductive types, fewer binders than parameters");
      const b = e as Expr & { kind: "pi" | "lam" };
      const x = fvar(b.binderName, instantiateRev(b.binderType, As));
      As.push(x);
      e = b.body;
    }
    e = instantiateRev(e, As);
    e = replace(e, (t) => {
      if (t.kind === "const") {
        const rn = auxRecMap.get(t.name);
        if (rn !== undefined) return constant(rn, t.levels);
      }
      const fn = getAppFn(t);
      if (fn.kind === "const") {
        const nested = this.aux2nested(fn.name);
        if (nested !== undefined) {
          const args = getAppArgs(t);
          if (args.length < this.params.length) fail("failed to restore nested inductive types");
          const newT = instantiateRev(abstract(nested, this.params), As);
          return apps(newT, args.slice(this.params.length));
        }
        const r = this.nestedIfAuxCtor(auxEnv, fn.name);
        if (r !== undefined) {
          const args = getAppArgs(t);
          if (args.length < this.params.length) fail("failed to restore nested inductive types");
          const newNested = instantiateRev(abstract(r[0], this.params), As);
          const I = getAppFn(newNested);
          if (I.kind !== "const") fail("failed to restore nested inductive types");
          const newFnName = replacePrefix(fn.name, r[1], (I as Expr & { kind: "const" }).name);
          return apps(apps(constant(newFnName, (I as Expr & { kind: "const" }).levels), getAppArgs(newNested)), args.slice(this.params.length));
        }
      }
      return undefined;
    });
    return isPi ? mkPi(As, e) : mkLambda(As, e);
  }
}

function appendName(prefix: Name, n: Name): Name {
  switch (n.kind) {
    case "anonymous":
      return prefix;
    case "str":
      return strName(appendName(prefix, n.prefix), n.str);
    case "num":
      return numName(appendName(prefix, n.prefix), n.num);
  }
}

// ---- Entry point -------------------------------------------------------------------------

function checkUniformIndOccs(decl: InductiveDecl): void {
  const names = decl.types.map((t) => t.name);
  const nparams = decl.numParams;
  for (const it of decl.types) {
    for (const c of it.ctors) {
      visit(c.type, (t, offset) => {
        const fn = getAppFn(t);
        if (fn.kind !== "const" || !names.includes(fn.name)) return true;
        const args = getAppArgs(t);
        if (args.length > nparams) return true;
        let ok =
          args.length === nparams &&
          offset >= nparams &&
          fn.levels.length === decl.levelParams.length &&
          fn.levels.every((l, i) => l.kind === "param" && l.name === decl.levelParams[i]);
        for (let i = 0; ok && i < nparams; i++) {
          const a = args[i]!;
          ok = a.kind === "bvar" && a.idx === offset - 1 - i;
        }
        if (!ok) fail(`invalid occurrence of datatype ${nameToString(fn.name)} being declared: it must be applied to the parameters and universe levels of the mutual declaration`);
        return false;
      });
    }
  }
}

function checkNoNestedAux(n: Name, e: Expr): void {
  if (exprAny(e, (t) => (t.kind === "const" && isPrefixOf(NESTED, t.name)) || (t.kind === "proj" && isPrefixOf(NESTED, t.typeName)))) {
    fail(`invalid declaration ${nameToString(n)}, it uses the reserved prefix _nested`);
  }
}

/**
 * Checks an inductive declaration against `env` and returns the constants it
 * introduces. `env` is not modified.
 */
export function addInductive(env: Environment, decl: InductiveDecl): InductiveResult {
  for (const it of decl.types) {
    checkNoFVar(it.name, it.type);
    checkNoNestedAux(it.name, it.type);
    for (const c of it.ctors) {
      checkNoFVar(c.name, c.type);
      checkNoNestedAux(c.name, c.type);
    }
  }
  checkUniformIndOccs(decl);
  const elim = new ElimNested(env, decl);
  const auxDecl = elim.run();
  const nnested = elim.nestedAux.length;
  const auxEnv = env.child();
  const aux = new AddInductive(auxEnv, auxDecl, nnested).run();
  if (nnested === 0) return aux;

  // Restore nested inductives.
  const ntypes = decl.types.length;
  const mainName = decl.types[0]!.name;
  const mainInfo = auxEnv.find(mainName) as InductiveInfo;
  const allNames = decl.types.map((t) => t.name);
  const auxRecNames: Name[] = [];
  const auxRecMap = new Map<Name, Name>();
  mainInfo.all.forEach((indName, i) => {
    if (i >= ntypes) {
      const old = recName(indName);
      auxRecNames.push(old);
      auxRecMap.set(old, appendAfter(recName(mainName), `_${i - ntypes + 1}`));
    }
  });
  const out: InductiveResult = { types: [], ctors: [], recs: [] };
  const processRec = (rn: Name): void => {
    const newRecName = auxRecMap.get(rn) ?? rn;
    const recInfo = auxEnv.find(rn) as RecursorInfo;
    const newType = elim.restoreNested(recInfo.type, auxEnv, auxRecMap);
    const rules = recInfo.rules.map((r) => ({
      ctor: newRecName !== rn ? elim.restoreCtorName(auxEnv, r.ctor) : r.ctor,
      nfields: r.nfields,
      rhs: elim.restoreNested(r.rhs, auxEnv, auxRecMap),
    }));
    out.recs.push({ ...recInfo, name: newRecName, type: newType, all: allNames, rules });
  };
  for (const it of decl.types) {
    const indInfo = auxEnv.find(it.name) as InductiveInfo;
    out.types.push({ ...indInfo, all: allNames });
    for (const cn of indInfo.ctors) {
      const ci = auxEnv.find(cn) as ConstructorInfo;
      out.ctors.push({ ...ci, type: elim.restoreNested(ci.type, auxEnv) });
    }
    processRec(recName(it.name));
  }
  for (const r of auxRecNames) processRec(r);

  // Check the restored declarations in an environment without the auxiliary types.
  const newEnv = env.child();
  for (const c of [...out.types, ...out.ctors, ...out.recs]) newEnv.add(c);
  const safety = decl.isUnsafe ? "unsafe" : "safe";
  {
    const tc = new TypeChecker(newEnv, { safety });
    for (const [nested] of elim.nestedAux) tc.check(nested, decl.levelParams);
  }
  {
    const tc = new TypeChecker(newEnv, { safety });
    for (const c of out.ctors) tc.check(c.type, decl.levelParams);
    for (const r of out.recs) {
      tc.check(r.type, r.levelParams);
      for (const rule of r.rules) tc.check(rule.rhs, r.levelParams);
    }
  }
  return out;
}
