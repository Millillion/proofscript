// Stub of the `proofscript` package for embedded mode.
//
// Every type here has a *simple* meaning to TypeScript (usually an alias of an
// ordinary type) and a *precise* meaning to the ProofScript checker. The runtime
// functions exist only so proof modules (`*.proof.ts`) are valid, loadable TS;
// implementation modules use `import type` and so never depend on this package.

// ---- Types: simple meaning for tsc, refined meaning for ProofScript ----------

/** A safe integer. TS: `number`. ProofScript: `{ x: number // Number.isSafeInteger(x) }`. */
export type int = number;
/** A non-negative safe integer. TS: `number`. ProofScript: `{ x: int // x >= 0 }`. */
export type nat = number;

/** Attaches a value index to a carrier type. TS: just `T`. */
export type Indexed<T, _Index> = T;

/** Index arithmetic. TS: `number`. ProofScript: the exact sum/product. */
export type Plus<_A extends number, _B extends number> = number;
export type Times<_A extends number, _B extends number> = number;

/** Base of all propositions defined as inductive families. Opaque to TS. */
export interface Prop {
  readonly __proofscript_prop: never;
}

/** A proof of something. Opaque to TS; ProofScript knows *what* it proves. */
export interface Proof {
  readonly __proofscript_proof: never;
}

/** A tactic. Opaque to TS. */
export interface Tactic {
  readonly __proofscript_tactic: never;
}

// ---- Runtime surface for proof modules --------------------------------------
// ProofScript reads the *source* of these calls; at runtime they are inert.

const inert = Object.freeze({}) as never;

/** `prove(statement, proof)`: the statement is a boolean expression over the
 * theorem's parameters. Run as plain TS it behaves like a property test:
 * calling the theorem with concrete inputs checks the statement for them. */
export function prove(statement: boolean, _proof: Tactic | (() => Proof)): Proof {
  if (!statement) throw new Error("ProofScript: theorem statement is false for these inputs");
  return inert;
}

/** A tactic script, Lean-style: `by(induction(xs), simp(length, append), omega)`. */
export function by(..._tactics: Tactic[]): Tactic & never {
  return inert;
}

export function implies(p: boolean, q: boolean): boolean {
  return !p || q;
}
/** Universal quantifier. Not executable in general; true at runtime. */
export function forall<A extends unknown[]>(_body: (...xs: A) => boolean): boolean {
  return true;
}
export function exists<A extends unknown[]>(_body: (...xs: A) => boolean): boolean {
  return true;
}

// Tactics (names follow Lean so Lean users and models transfer directly).
export const omega: Tactic = inert;
export const rfl: Tactic & Proof = inert;

export function cases(_target: unknown): Tactic { return inert; }
export function simp(..._lemmas: unknown[]): Tactic { return inert; }
export function exact(_proof: unknown): Tactic { return inert; }

/** `induction(target, cases)`: one callback per constructor. Callback
 * parameters name the constructor's fields and induction hypotheses, so
 * hypotheses are ordinary TS bindings rather than names invented by a tactic. */
export function induction(_target: unknown, _cases?: Record<string, (...args: any[]) => Tactic | Proof>): Tactic {
  return inert;
}
/** Congruence: from a proof of `a === b`, a proof of `f(a) === f(b)`. */
export function congrArg<A>(_f: (a: A) => unknown, _h: Proof): Proof {
  return inert;
}
