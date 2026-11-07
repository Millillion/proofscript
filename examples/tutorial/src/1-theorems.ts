// Step 1: theorems. A theorem is a function returning `Proof`; its body states a
// boolean fact with `prove` and says how to prove it with a tactic.
import { by, grind, implies, induction, omega, prove, simp_all, unfold, type Nat, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

// `implies(p, q)`: if p then q. Hypotheses are just booleans.
export function lt_of_lt_of_le(a: nat, b: nat, c: nat): Proof {
  return prove(implies(a < b && b <= c, a < c), omega);
}

// Calling a theorem runs its statement on concrete inputs: a property test for free.
// (`add_comm(2, 3)` returns normally; a false statement would throw.)

// `nat` is a JavaScript number: n + sum_to(n - 1) could pass 2^53 and lose precision,
// and ProofScript would reject it. `Nat` (a bigint) is exact, for mathematics.
export function sum_to(n: Nat): Nat {
  return n === 0n ? 0n : n + sum_to(n - 1n);
}

// Induction over a natural number: Lean's `induction n with | zero => … | succ k ih => …`.
export function gauss(n: Nat): Proof {
  return prove(
    2n * sum_to(n) === n * (n + 1n),
    by(induction(n, {
      zero: () => simp_all(sum_to),
      succ: (_k, _ih) => by(unfold(sum_to), grind),
    })),
  );
}
