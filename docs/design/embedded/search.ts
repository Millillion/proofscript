import type { int } from "./proofscript/index.ts";

export function isSorted(a: readonly int[]): boolean {
  for (let i = 0; i + 1 < a.length; i++) {
    //@ invariant forall((j: nat) => j < i ==> a[j] <= a[j + 1])
    if (a[i] > a[i + 1]) return false;
  }
  return true;
}

//@ requires isSorted(a)
//@ ensures r => (r >= 0 ==> a[r] === key) && (r < 0 ==> !a.includes(key))
export function binarySearch(a: readonly int[], key: int): int {
  let lo = 0, hi = a.length;
  while (lo < hi) {
    //@ invariant 0 <= lo && lo <= hi && hi <= a.length
    //@ invariant forall((i: nat) => (i < lo || (hi <= i && i < a.length)) ==> a[i] !== key)
    //@ decreases hi - lo
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
