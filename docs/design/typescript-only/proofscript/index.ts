// The `proofscript` package.
//
// ProofScript is written entirely in TypeScript. Every type below has a simple
// meaning to `tsc` (usually `number` or `unknown`) and a precise meaning to the
// ProofScript checker, which recognizes these declarations by symbol (they must
// come from this package), never by name.
//
// Modules without theorems import only types from here (`import type`). Modules
// with theorems also use the runtime functions at the bottom; these never run in
// a real program, because nothing calls a theorem. Called directly (for example
// from a test), a theorem checks its statement on the given inputs: a property
// test. This package is side-effect free, so bundlers drop it along with
// unreferenced theorems.

// ---- Numbers -------------------------------------------------------------------------

/** TS: `number`. ProofScript: a safe integer (`Number.isSafeInteger`). Exact in specs. */
export type int = number;
/** TS: `number`. ProofScript: a safe integer `>= 0`. Exact in specs. */
export type nat = number;
/** Mathematical natural numbers, unbounded (ghost: for theorems, never for running code). */
export type Nat = bigint;
/** Mathematical integers, unbounded (ghost: for theorems, never for running code). */
export type Int = bigint;

// ---- Refinements -----------------------------------------------------------------------
// A refinement is an intersection `T & R`. To TS, every `R` below is `unknown`, so
// `T & R` is just `T`. To ProofScript, `T & R` is `{ x: T // R holds of x }`.
// Parameter refinements are preconditions; return-type refinements are
// postconditions; `x satisfies R;` statements are assertions and loop invariants.

/** `x < N`. */
export type Lt<_N extends number | bigint> = unknown;
/** `x <= N`. */
export type Le<_N extends number | bigint> = unknown;
/** `x > N`. */
export type Gt<_N extends number | bigint> = unknown;
/** `x >= N`. */
export type Ge<_N extends number | bigint> = unknown;
/** `x.length === N`. */
export type Length<_N extends number> = unknown;

/** `pred(x, ...args)` holds, for an ordinary TypeScript predicate function. */
export type Is<_Pred extends (x: any, ...args: Args) => boolean, Args extends unknown[] = []> = unknown;

/** In `e satisfies Decreases;` at the top of a function or loop body: a termination measure. */
export type Decreases = unknown;

/** In `null satisfies Use<typeof lemma, [typeof a, …]>;`: instantiate a lemma at this point. */
export type Use<_Lemma extends (...args: Args) => unknown, Args extends unknown[] = []> = unknown;

// ---- Value indices -----------------------------------------------------------------------
// Type parameters `n extends nat` range over numeric literal types, i.e. values.
// `typeof x` in an index position means "exactly the value x".

/** TS: `number`. ProofScript: the exact sum. */
export type Plus<_A extends number, _B extends number> = number;
/** TS: `number`. ProofScript: the exact product. */
export type Times<_A extends number, _B extends number> = number;

// ---- Propositions and proofs (Curry–Howard) -------------------------------------------------

/** Base of inductive families of propositions. Opaque to TS. */
export interface Prop {
  readonly __proofscript_prop: never;
}
/** A proof of a theorem stated with `prove`. Opaque to TS. */
export interface Proof {
  readonly __proofscript_proof: never;
}
/** A tactic. Opaque to TS. */
export interface Tactic {
  readonly __proofscript_tactic: never;
}
/** Attribute: `Proof & Simp` is Lean's `@[simp] theorem`. To TS, `unknown`. */
export type Simp = unknown;

// ---- Runtime surface for theorems -----------------------------------------------------------

const inert = Object.freeze({}) as never;

/** `prove(statement, proof)`: the statement is an ordinary boolean expression over the
 * theorem's parameters. Called directly, it checks the statement for those inputs. */
export function prove(statement: boolean, _proof: Tactic | (() => Proof | Tactic)): Proof {
  if (!statement) throw new Error("ProofScript: theorem statement is false for these inputs");
  return inert;
}

/** A tactic script. Semantics are exactly Lean's: `by(t1, t2)` runs `t1`, then `t2` on the first goal. */
export function by(..._tactics: Tactic[]): Tactic & never {
  return inert;
}

/** Implication. */
export function implies(p: boolean, q: boolean): boolean {
  return !p || q;
}
/** If and only if. */
export function iff(p: boolean, q: boolean): boolean {
  return p === q;
}
/** Structural (propositional) equality. At runtime, a deep comparison. */
export function eq<T>(a: T, b: T): boolean {
  return JSON.stringify(a) === JSON.stringify(b);
}
/** Universal quantifier (bounded ones are just `Array.prototype.every`). Not executable: true at runtime. */
export function forall<A extends unknown[]>(_body: (...xs: A) => boolean): boolean {
  return true;
}
/** Existential quantifier. Not executable: true at runtime. */
export function exists<A extends unknown[]>(_body: (...xs: A) => boolean): boolean {
  return true;
}

// Tactics. Names and behaviour are Lean's.
export const omega: Tactic = inert;
export const rfl: Tactic & Proof = inert;
export const decide: Tactic = inert;
export const trivial: Tactic = inert;
export const constructor: Tactic = inert;
export const grind: Tactic = inert;
/** An unproved hole. Allowed, and always reported (the theorem is "admitted", not "verified"). */
export const sorry: Tactic & Proof = inert;

/** `induction(x, { ctor: (fields…, ihs…) => tactic })`: callback parameters name the
 * constructor's fields and induction hypotheses, as Lean's `induction x with | ctor a b ih => …`. */
export function induction(_target: unknown, _cases?: Record<string, (...args: any[]) => Tactic | Proof>): Tactic {
  return inert;
}
export function cases(_target: unknown, _cases?: Record<string, (...args: any[]) => Tactic | Proof>): Tactic {
  return inert;
}
export function simp(..._lemmas: unknown[]): Tactic {
  return inert;
}
export function simp_all(..._lemmas: unknown[]): Tactic {
  return inert;
}
export function rw(..._lemmas: unknown[]): Tactic {
  return inert;
}
/** Lean's `unfold f`: replace `f` by its definition. */
export function unfold(..._defs: unknown[]): Tactic {
  return inert;
}
export function exact(_proof: unknown): Tactic {
  return inert;
}
export function apply(_proof: unknown): Tactic {
  return inert;
}
export function intro(..._names: string[]): Tactic {
  return inert;
}
/** Lean's `all_goals`. */
export function allGoals(_t: Tactic): Tactic {
  return inert;
}
/** From `a === b`, `f(a) === f(b)`. */
export function congrArg<A>(_f: (a: A) => unknown, _h: Proof): Proof {
  return inert;
}
