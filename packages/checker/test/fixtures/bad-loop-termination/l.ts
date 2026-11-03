import type { Ge, Le, nat } from "proofscript";

// i never changes: the loop does not terminate when n > 0. Must not verify.
export function f(n: nat): nat & Ge<0> {
  let i = 0;
  while (i < n) {
    i satisfies Le<typeof n>;
    n satisfies Ge<0>;
  }
  return i;
}
