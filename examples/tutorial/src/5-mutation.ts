// Step 5: mutation. `Modifies<typeof a>` declares what a function may change;
// `Old<typeof a>` is the value on entry. Writes are proved in bounds.
import type { Holds, Lt, Modifies, Old, nat } from "proofscript";

export function swapped(b: readonly nat[], a: readonly nat[], i: nat, j: nat): boolean {
  if (i < a.length && j < a.length && b.length === a.length) return b[i] === a[j] && b[j] === a[i];
  return false;
}

export function swap(
  a: nat[],
  i: nat & Lt<typeof a.length>,
  j: nat & Lt<typeof a.length>,
): void & Modifies<typeof a> & Holds<typeof swapped, [typeof a, Old<typeof a>, typeof i, typeof j]> {
  const t = a[i];
  a[i] = a[j];
  a[j] = t;
}
