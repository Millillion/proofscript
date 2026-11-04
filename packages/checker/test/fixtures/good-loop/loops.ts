import type { Decreases, Ge, Is, Le, Lt, nat } from "proofscript";

export function isTripleOf(s: nat, n: nat & Lt<1000000000000000>): boolean {
  return s === 3 * n;
}

// triple(n) === 3n, carried by the invariant `s === 3 * i`. The bound on n keeps
// every intermediate value below 2^53, which ProofScript proves for each step.
export function triple(n: nat & Lt<1000000000000000>): nat & Is<typeof isTripleOf, [typeof n]> {
  let s = 0;
  let i = 0;
  while (i < n) {
    i satisfies Le<typeof n>;
    s satisfies Is<typeof isTripleOf, [typeof i]>;
    n - i satisfies Decreases;
    s = s + 3;
    i = i + 1;
  }
  return s;
}

// A for loop over an array: every index is proved in bounds.
export function maxOf(a: readonly nat[]): nat & Ge<0> {
  let m = 0;
  for (let i = 0; i < a.length; i++) {
    i satisfies Le<typeof a.length>;
    a.length - i satisfies Decreases;
    if (a[i] > m) m = a[i];
  }
  return m;
}
