import type { Decreases, Le, Length, Lt, nat } from "./proofscript/index.ts";

// Value-indexed types: to TypeScript, arrays and numbers; to ProofScript, an array of
// length exactly n, and a number below n.
export type Vec<T, n extends nat> = readonly T[] & Length<n>;
export type Fin<n extends nat> = nat & Lt<n>;

// Dependent return type: `typeof n` is `number` to TS, "exactly n" to ProofScript.
// (n < 2^32 because JavaScript arrays are shorter than that.)
export function replicate<T>(n: nat & Lt<4294967296>, x: T): Vec<T, typeof n> {
  const out: T[] = [];
  for (let i = 0; i < n; i++) {
    i satisfies Le<typeof n>;
    out satisfies Length<typeof i>;
    n - i satisfies Decreases;
    out.push(x);
  }
  return out;
}

// `n` is never passed: it is xs.length, and ys must have the same length.
export function zip<A, B, n extends nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> {
  const out: [A, B][] = [];
  for (let i = 0; i < xs.length; i++) {
    i satisfies Le<typeof xs.length>;
    out satisfies Length<typeof i>;
    xs.length - i satisfies Decreases;
    out.push([xs[i], ys[i]]);
  }
  return out;
}

// No bounds check needed: `i < n === xs.length` is part of the types.
export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T {
  return xs[i];
}
