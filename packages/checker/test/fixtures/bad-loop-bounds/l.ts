import type { Decreases, Ge, Le, nat } from "proofscript";

// Reads a[i + 1], which is out of bounds on the last iteration (undefined in JS). Must not verify.
export function f(a: readonly nat[]): nat & Ge<0> {
  let m = 0;
  for (let i = 0; i < a.length; i++) {
    i satisfies Le<typeof a.length>;
    a.length - i satisfies Decreases;
    m = m + a[i + 1];
  }
  return m;
}
