import type { Decreases, Ge, Is, Le, nat } from "proofscript";

export function isSquareOf(s: nat, n: nat): boolean {
  return s === n * n;
}

// The sum of the first n odd numbers is n². The invariant `s === i * i` carries it.
export function sumOdds(n: nat): nat & Is<typeof isSquareOf, [typeof n]> {
  let s = 0;
  let i = 0;
  while (i < n) {
    i satisfies Le<typeof n>;
    s satisfies Is<typeof isSquareOf, [typeof i]>;
    n - i satisfies Decreases;
    s = s + 2 * i + 1;
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
