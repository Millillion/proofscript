import type { Holds, Lt, Modifies, Old, nat } from "proofscript";

export function unchangedAt(b: readonly nat[], a: readonly nat[], i: nat): boolean {
  if (i < a.length && b.length === a.length) return b[i] === a[i];
  return false;
}

// Wrong: a[i] does change. Must not verify.
export function setZero(a: nat[], i: nat & Lt<typeof a.length>): void & Modifies<typeof a> & Holds<typeof unchangedAt, [typeof a, Old<typeof a>, typeof i]> {
  a[i] = a[i] + 1;
}
