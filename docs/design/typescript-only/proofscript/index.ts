// Stub of the `proofscript` package.
//
// ProofScript is written entirely in TypeScript. Every type below has a simple
// meaning to `tsc` (usually `number` or `unknown`) and a precise meaning to the
// ProofScript checker, which recognizes these declarations by symbol, not name.
// Implementation modules import only types from here (`import type`), so they
// have no runtime dependency on ProofScript. Proof modules (`*.proof.ts`) also
// use the inert runtime functions at the bottom.

// ---- Numbers -----------------------------------------------------------------

/** TS: `number`. ProofScript: a safe integer (`Number.isSafeInteger`). */
export type int = number;
/** TS: `number`. ProofScript: a safe integer `>= 0`. */
export type nat = number;

// ---- Refinements ---------------------------------------------------------------
// A refinement is an intersection `T & R`. To TS, every `R` below is `unknown`,
// so `T & R` is just `T`. To ProofScript, `T & R` is `{ x: T // R holds of x }`.
// Parameter refinements are preconditions; return-type refinements are
// postconditions; `x satisfies R` statements are assertions and invariants.

/** `x < N`. */ export type Lt<_N extends number | bigint> = unknown;
/** `x <= N`. */ export type Le<_N extends number | bigint> = unknown;
/** `x > N`. */ export type Gt<_N extends number | bigint> = unknown;
/** `x >= N`. */ export type Ge<_N extends number | bigint> = unknown;
/** `x.length === N`. */ export type Length<_N extends number> = unknown;

/** `pred(x, ...args)` holds, for an ordinary TS predicate function.
 * `tsc` checks that `pred` accepts the refined value and the arguments. */
export type Is<
  _Pred extends (x: any, ...args: Args) => boolean,
  Args extends unknown[] = [],
> = unknown;

/** In `e satisfies Decreases` at the top of a loop: a termination measure. */
export type Decreases = unknown;

/** In `null satisfies Use<typeof lemma, [typeof a, ...]>`: instantiate a lemma
 * here, adding its conclusion to what the checker knows. */
export type Use<_Lemma extends (...args: Args) => unknown, Args extends unknown[] = []> = unknown;

// ---- Value indices ---------------------------------------------------------------
// Type parameters `n extends nat` range over numeric literal types, i.e. values.
// `typeof x` in an index position means "exactly the value x".

/** TS: `number`. ProofScript: the exact sum. */
export type Plus<_A extends number, _B extends number> = number;

// ---- Propositions and proofs (Curry–Howard) ---------------------------------------

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

// ---- Runtime surface for proof modules only ----------------------------------------
// ProofScript reads the *source* of these calls; at runtime they are inert, except
// that `prove` checks its statement, so a theorem run as TS is a property test.

const inert = Object.freeze({}) as never;

export function prove(statement: boolean, _proof: Tactic | (() => Proof | Tactic)): Proof {
  if (!statement) throw new Error("ProofScript: theorem statement is false for these inputs");
  return inert;
}
export function by(..._tactics: Tactic[]): Tactic & never {
  return inert;
}
export function implies(p: boolean, q: boolean): boolean {
  return !p || q;
}
/** Unbounded universal quantifier (bounded ones are just `Array.prototype.every`). */
export function forall<A extends unknown[]>(_body: (...xs: A) => boolean): boolean {
  return true;
}

// Tactics: Lean's names, so Lean users (and models trained on Lean) transfer directly.
export const omega: Tactic = inert;
export const rfl: Tactic & Proof = inert;
/** One callback per constructor; callback parameters name fields and induction
 * hypotheses, so every hypothesis is an ordinary TS binding. */
export function induction(_target: unknown, _cases?: Record<string, (...args: any[]) => Tactic | Proof>): Tactic {
  return inert;
}
export function simp(..._lemmas: unknown[]): Tactic {
  return inert;
}
export function exact(_proof: unknown): Tactic {
  return inert;
}
export function congrArg<A>(_f: (a: A) => unknown, _h: Proof): Proof {
  return inert;
}
