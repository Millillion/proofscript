// Step 4: loops. `x satisfies R;` at the top of a loop body is an invariant, and
// `e satisfies Decreases;` a termination measure. Array indices are proved in bounds.
import type { Decreases, Ge, Le, nat } from "proofscript";

export function countBelow(a: readonly nat[], limit: nat): nat & Le<typeof a.length> {
  let c = 0;
  for (let i = 0; i < a.length; i++) {
    i satisfies Le<typeof a.length>;
    c satisfies Le<typeof i>;
    a.length - i satisfies Decreases;
    if (a[i] < limit) c = c + 1;
  }
  return c;
}

// A while loop.
export function largest(a: readonly nat[]): nat & Ge<0> {
  let m = 0;
  let i = 0;
  while (i < a.length) {
    i satisfies Le<typeof a.length>;
    a.length - i satisfies Decreases;
    if (a[i] > m) m = a[i];
    i = i + 1;
  }
  return m;
}
