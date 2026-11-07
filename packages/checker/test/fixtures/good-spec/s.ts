import { forall, implies, type Decreases, type Holds, type Le, type Modifies, type nat } from "proofscript";

export function f(p: nat): nat {
  return ((p % 64) * 7) % 64;
}

// A specification predicate: every element before `j` is f of its position.
export function filledUpTo(out: readonly nat[], j: nat): boolean {
  return forall((p: nat) => implies(p < j && p < out.length, out[p] === f(p)));
}

export function filled(out: readonly nat[]): boolean {
  return forall((p: nat) => implies(p < out.length, out[p] === f(p)));
}

// Fill `out` in place; the quantified invariant carries the postcondition.
export function fill(out: nat[]): void & Modifies<typeof out> & Holds<typeof filled, [typeof out]> {
  let j = 0;
  while (j < out.length) {
    j satisfies Le<typeof out.length>;
    out satisfies Holds<typeof filledUpTo, [typeof out, typeof j]>;
    out.length - j satisfies Decreases;
    out[j] = f(j);
    j = j + 1;
  }
}
