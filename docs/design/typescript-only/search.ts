import type { Decreases, int, Is, Le, nat } from "./proofscript/index.ts";

// Specs are ordinary, executable TypeScript predicates.
export function isSorted(a: readonly int[]): boolean {
  return a.every((x, i) => i === 0 || a[i - 1] <= x);
}
export type Sorted = readonly int[] & Is<typeof isSorted>;

const found = (r: int, a: readonly int[], key: int): boolean => (r >= 0 ? a[r] === key : !a.includes(key));
const notInOuter = (key: int, a: readonly int[], lo: nat, hi: nat): boolean =>
  a.every((x, i) => (lo <= i && i < hi) || x !== key);

// Precondition: the parameter type `Sorted`. Postcondition: the return type.
export function binarySearch(a: Sorted, key: int): int & Is<typeof found, [typeof a, typeof key]> {
  let lo = 0, hi = a.length;
  while (lo < hi) {
    // Loop invariants and the termination measure: `satisfies` statements.
    // Each erases to a bare expression statement (`lo;`) with no runtime effect.
    lo satisfies nat & Le<typeof hi>;
    hi satisfies nat & Le<typeof a.length>;
    key satisfies Is<typeof notInOuter, [typeof a, typeof lo, typeof hi]>;
    hi - lo satisfies Decreases;
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
