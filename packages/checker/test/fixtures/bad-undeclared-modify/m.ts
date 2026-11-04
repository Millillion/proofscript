import type { Holds, Old, nat } from "proofscript";

// Changes its argument without declaring `Modifies`.
export function clearFirst(a: nat[]): boolean {
  if (a.length > 0) a[0] = 0;
  return true;
}

export function same(b: readonly nat[], a: readonly nat[]): boolean {
  return b.length === a.length;
}

// A verified caller: translating clearFirst must reject its undeclared mutation.
export function caller(a: nat[]): boolean & Holds<typeof same, [typeof a, typeof a]> {
  return clearFirst(a);
}
