import type { Decreases, Ge, Le, nat } from "proofscript";

// The invariant `s <= i` is not preserved (s grows by 2 per step). Must not verify.
export function f(n: nat): nat & Ge<0> {
  let s = 0;
  let i = 0;
  while (i < n) {
    i satisfies Le<typeof n>;
    s satisfies Le<typeof i>;
    n - i satisfies Decreases;
    s = s + 2;
    i = i + 1;
  }
  return s;
}
