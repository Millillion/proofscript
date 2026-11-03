import type { Le, Length, Lt, nat } from "./proofscript/index.ts";

// Value-indexed type: to TS a readonly array, to ProofScript an array of length exactly n.
export type Vec<T, n extends nat> = readonly T[] & Length<n>;

// Dependent return type: `typeof n` is `number` to TS, "exactly n" to ProofScript.
export function replicate<T>(n: nat, x: T): Vec<T, typeof n> {
  const out: T[] = [];
  for (let i = 0; i < n; i++) {
    i satisfies Le<typeof n>;
    out satisfies Length<typeof i>;
    out.push(x);
  }
  return out;
}

export function zip<A, B, n extends nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> {
  const out: [A, B][] = [];
  for (let i = 0; i < xs.length; i++) {
    out satisfies Length<typeof i>;
    out.push([xs[i], ys[i]]);
  }
  return out;
}

// A precondition relating two parameters. No bounds check needed in the body.
export function get<T>(xs: readonly T[], i: nat & Lt<typeof xs.length>): T {
  return xs[i];
}
