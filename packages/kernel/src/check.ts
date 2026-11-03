// Adding declarations to an environment: the kernel's entry point.
//
// Every constant that enters the environment has been checked here. Data that
// an export file supplies but the kernel can derive (recursors, inductive
// metadata, the quotient constants) is re-derived and compared, never trusted.

import {
  type ConstantInfo,
  type Declaration,
  type DefinitionInfo,
  Environment,
  type InductiveInfo,
  KernelError,
  type QuotInfo,
  isUnsafe,
} from "./env.ts";
import { type Expr, app, apps, bvar, constant, exprEq, pi, sort } from "./expr.ts";
import { type IndType, addInductive } from "./inductive.ts";
import { type Level, param, zero } from "./level.ts";
import { type Name, name, nameToString } from "./name.ts";
import { TypeChecker } from "./typechecker.ts";

const fail = (msg: string): never => {
  throw new KernelError(msg);
};

function checkNoFVar(n: Name, e: Expr): void {
  if (e.hasFVar || e.lbr > 0) fail(`declaration ${nameToString(n)} is not closed`);
}

export class Kernel {
  readonly env: Environment;
  /** Unsafe/partial definitions whose mutual block is not complete yet. */
  readonly #pending: DefinitionInfo[] = [];

  constructor(env: Environment = new Environment()) {
    this.env = env;
  }

  /** Checks the constant's name, universe parameters and type (which must be a type). */
  #checkHeader(c: ConstantInfo, tc: TypeChecker, env: Environment = this.env): void {
    if (env.has(c.name)) fail(`${nameToString(c.name)} has already been declared`);
    if (new Set(c.levelParams).size !== c.levelParams.length) fail(`duplicate universe level parameter in ${nameToString(c.name)}`);
    checkNoFVar(c.name, c.type);
    tc.ensureSort(tc.check(c.type, c.levelParams));
  }

  #checkValue(c: ConstantInfo & { value: Expr }, tc: TypeChecker): void {
    checkNoFVar(c.name, c.value);
    const t = tc.check(c.value, c.levelParams);
    if (!tc.isDefEq(t, c.type)) fail(`type mismatch in the value of ${nameToString(c.name)}`);
  }

  add(d: Declaration): void {
    if (this.#pending.length > 0 && d.kind !== "definition") {
      fail(`incomplete mutual definition block ${this.#pending.map((p) => nameToString(p.name)).join(", ")}`);
    }
    switch (d.kind) {
      case "axiom": {
        const tc = new TypeChecker(this.env, { safety: d.info.isUnsafe ? "unsafe" : "safe" });
        this.#checkHeader(d.info, tc);
        this.env.add(d.info);
        return;
      }
      case "definition":
        return this.#addDefinition(d.info);
      case "theorem": {
        const tc = new TypeChecker(this.env);
        this.#checkHeader(d.info, tc);
        if (!tc.isProp(d.info.type)) fail(`type of theorem ${nameToString(d.info.name)} is not a proposition`);
        this.#checkValue(d.info, tc);
        this.env.add(d.info);
        return;
      }
      case "opaque": {
        const tc = new TypeChecker(this.env, { safety: d.info.isUnsafe ? "unsafe" : "safe" });
        this.#checkHeader(d.info, tc);
        this.#checkValue(d.info, tc);
        this.env.add(d.info);
        return;
      }
      case "quot":
        return this.#addQuot(d.infos);
      case "inductive":
        return this.#addInductive(d.types, d.ctors, d.recs);
    }
  }

  #addDefinition(info: DefinitionInfo): void {
    if (info.safety === "safe") {
      const tc = new TypeChecker(this.env);
      this.#checkHeader(info, tc);
      this.#checkValue(info, tc);
      this.env.add(info);
      return;
    }
    // Unsafe and partial definitions may be (mutually) recursive: check every header,
    // add the whole block, then check the values.
    const block = [...this.#pending, info];
    const first = block[0]!;
    if (block.some((b) => b.safety !== first.safety)) fail("mutual definitions must have the same safety annotation");
    const names = first.all;
    if (block.some((b) => b.all.length !== names.length || b.all.some((n, i) => n !== names[i]))) {
      fail("mutual definitions must agree on the block");
    }
    if (!names.includes(info.name)) fail(`${nameToString(info.name)} is not in its own mutual block`);
    if (block.length < names.length) {
      this.#pending.push(info);
      return;
    }
    this.#pending.length = 0;
    if (new Set(block.map((b) => b.name)).size !== block.length) fail("duplicate declaration in mutual block");
    const lps = first.levelParams;
    const scratch = this.env.child();
    for (const b of block) {
      if (b.levelParams.length !== lps.length || b.levelParams.some((n, i) => n !== lps[i])) {
        fail("mutual definitions must have the same universe level parameters");
      }
      this.#checkHeader(b, new TypeChecker(this.env, { safety: b.safety }), scratch);
    }
    for (const b of block) scratch.add(b);
    const tc = new TypeChecker(scratch, { safety: first.safety });
    for (const b of block) this.#checkValue(b, tc);
    scratch.commit();
  }

  #addQuot(infos: readonly QuotInfo[]): void {
    if (this.env.quotInitialized) fail("quotient types already initialized");
    checkEqType(this.env);
    const expected = quotConstants();
    if (infos.length !== expected.length) fail("malformed quotient declaration");
    // Like Lean, the kernel installs its own quotient constants; the types an
    // export claims for them are redundant and ignored (never trusted).
    for (const e of expected) {
      const got = infos.find((i) => i.name === e.name);
      if (got === undefined || got.quotKind !== e.quotKind) fail(`malformed quotient declaration: missing ${nameToString(e.name)}`);
      if (this.env.has(e.name)) fail(`${nameToString(e.name)} has already been declared`);
    }
    for (const e of expected) this.env.add(e);
    this.env.quotInitialized = true;
  }

  #addInductive(types: readonly InductiveInfo[], ctors: readonly ConstantInfo[], recs: readonly ConstantInfo[]): void {
    if (types.length === 0) fail("empty inductive declaration");
    const t0 = types[0]!;
    for (const t of types) {
      if (t.numParams !== t0.numParams || !sameNames(t.levelParams, t0.levelParams) || t.isUnsafe !== t0.isUnsafe) {
        fail("inconsistent mutual inductive declaration");
      }
    }
    const byName = new Map<Name, ConstantInfo>();
    for (const c of ctors) {
      if (byName.has(c.name)) fail(`duplicate constructor ${nameToString(c.name)}`);
      byName.set(c.name, c);
    }
    const indTypes: IndType[] = types.map((t) => ({
      name: t.name,
      type: t.type,
      ctors: t.ctors.map((cn) => {
        const c = byName.get(cn);
        if (c === undefined) return fail(`missing constructor ${nameToString(cn)}`);
        byName.delete(cn);
        return { name: c.name, type: c.type };
      }),
    }));
    if (byName.size > 0) fail("constructor does not belong to any declared type");
    const result = addInductive(this.env, { levelParams: t0.levelParams, numParams: t0.numParams, types: indTypes, isUnsafe: t0.isUnsafe });
    // Compare everything the export claims with what the kernel derived.
    const ours = [...result.types, ...result.ctors, ...result.recs];
    const theirs = [...types, ...ctors, ...recs];
    if (ours.length !== theirs.length) fail("inductive declaration does not match the derived constants");
    for (const c of theirs) {
      const o = ours.find((x) => x.name === c.name);
      if (o === undefined || !sameConstant(o, c)) fail(`${nameToString(c.name)} does not match the constant the kernel derives`);
    }
    for (const c of ours) this.env.add(c);
  }

  /** Finishes checking: rejects an incomplete mutual block. */
  finish(): void {
    if (this.#pending.length > 0) fail("incomplete mutual definition block at end of input");
  }
}

function sameNames(a: readonly Name[], b: readonly Name[]): boolean {
  return a.length === b.length && a.every((n, i) => n === b[i]);
}

function sameConstant(a: ConstantInfo, b: ConstantInfo): boolean {
  if (a.kind !== b.kind || a.name !== b.name || !sameNames(a.levelParams, b.levelParams) || !exprEq(a.type, b.type)) return false;
  if (isUnsafe(a) !== isUnsafe(b)) return false;
  switch (a.kind) {
    case "inductive": {
      const c = b as typeof a;
      return (
        a.numParams === c.numParams &&
        a.numIndices === c.numIndices &&
        sameNames(a.all, c.all) &&
        sameNames(a.ctors, c.ctors) &&
        a.numNested === c.numNested &&
        a.isRec === c.isRec &&
        a.isReflexive === c.isReflexive
      );
    }
    case "constructor": {
      const c = b as typeof a;
      return a.induct === c.induct && a.cidx === c.cidx && a.numParams === c.numParams && a.numFields === c.numFields;
    }
    case "recursor": {
      const c = b as typeof a;
      return (
        sameNames(a.all, c.all) &&
        a.numParams === c.numParams &&
        a.numIndices === c.numIndices &&
        a.numMotives === c.numMotives &&
        a.numMinors === c.numMinors &&
        a.k === c.k &&
        a.rules.length === c.rules.length &&
        a.rules.every((r, i) => {
          const s = c.rules[i]!;
          return r.ctor === s.ctor && r.nfields === s.nfields && exprEq(r.rhs, s.rhs);
        })
      );
    }
    default:
      return false;
  }
}

// ---- Quotients ------------------------------------------------------------------------

const Eq = name("Eq");
const Prop = sort(zero);

function arrow(a: Expr, b: Expr): Expr {
  return pi(name("a"), a, b);
}

/** `Eq` must be the usual inductive equality before quotients can be added. */
function checkEqType(env: Environment): void {
  const eq = env.get(Eq);
  if (eq === undefined || eq.kind !== "inductive") return fail("quotient types require the Eq type");
  if (eq.levelParams.length !== 1 || eq.ctors.length !== 1) fail("unexpected Eq type");
  const u = param(eq.levelParams[0]!);
  // {α : Sort u} → α → α → Prop
  const expected = pi(name("α"), sort(u), arrow(bvar(0), arrow(bvar(1), Prop)), "implicit");
  if (!exprEq(eq.type, expected)) fail("Eq has an unexpected type");
  const refl = env.find(eq.ctors[0]!);
  if (refl.levelParams.length !== 1) fail("unexpected Eq constructor");
  const v = param(refl.levelParams[0]!);
  // {α : Sort u} → (a : α) → @Eq α a a
  const expectedRefl = pi(name("α"), sort(v), pi(name("a"), bvar(0), apps(constant(Eq, [v]), [bvar(1), bvar(0), bvar(0)])), "implicit");
  if (!exprEq(refl.type, expectedRefl)) fail("Eq.refl has an unexpected type");
}

function quotConstants(): QuotInfo[] {
  const u = name("u");
  const v = name("v");
  const U: Level = param(u);
  const V: Level = param(v);
  const quot = (alpha: Expr, r: Expr) => apps(constant(name("Quot"), [U]), [alpha, r]);
  // Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u
  const quotType = pi(name("α"), sort(U), pi(name("r"), rel0(), sort(U)), "implicit");
  // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → @Quot α r
  const mkType = pi(name("α"), sort(U), pi(name("r"), rel0(), pi(name("a"), bvar(1), quot(bvar(2), bvar(1)))), "implicit");
  // Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) →
  //   (∀ a b : α, r a b → f a = f b) → @Quot α r → β
  const sanity = pi(
    name("a"),
    bvar(3),
    pi(name("b"), bvar(4), arrow(apps(bvar(4), [bvar(1), bvar(0)]), apps(constant(Eq, [V]), [bvar(4), app(bvar(3), bvar(2)), app(bvar(3), bvar(1))]))),
  );
  const liftType = pi(
    name("α"),
    sort(U),
    pi(
      name("r"),
      rel0(),
      pi(name("β"), sort(V), pi(name("f"), arrow(bvar(2), bvar(1)), arrow(sanity, arrow(quot(bvar(4), bvar(3)), bvar(3)))), "implicit"),
      "implicit",
    ),
    "implicit",
  );
  // Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} → {β : @Quot α r → Prop} →
  //   (mk : ∀ a : α, β (@Quot.mk α r a)) → ∀ q : @Quot α r, β q
  const mkApp = (alpha: Expr, r: Expr, a: Expr) => apps(constant(name("Quot.mk"), [U]), [alpha, r, a]);
  const indType = pi(
    name("α"),
    sort(U),
    pi(
      name("r"),
      rel0(),
      pi(
        name("β"),
        arrow(quot(bvar(1), bvar(0)), Prop),
        pi(name("mk"), pi(name("a"), bvar(2), app(bvar(1), mkApp(bvar(3), bvar(2), bvar(0)))), pi(name("q"), quot(bvar(3), bvar(2)), app(bvar(2), bvar(0)))),
        "implicit",
      ),
      "implicit",
    ),
    "implicit",
  );
  return [
    { kind: "quot", name: name("Quot"), levelParams: [u], type: quotType, quotKind: "type" },
    { kind: "quot", name: name("Quot.mk"), levelParams: [u], type: mkType, quotKind: "ctor" },
    { kind: "quot", name: name("Quot.lift"), levelParams: [u, v], type: liftType, quotKind: "lift" },
    { kind: "quot", name: name("Quot.ind"), levelParams: [u], type: indType, quotKind: "ind" },
  ];
}

/** `α → α → Prop` where α is `bvar 0`. */
function rel0(): Expr {
  return arrow(bvar(0), arrow(bvar(1), Prop));
}

