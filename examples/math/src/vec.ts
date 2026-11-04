import { prove, omega, type Decreases, type Le, type Length, type Lt, type nat, type Proof } from "proofscript";

// Value-indexed types: to TypeScript, arrays and numbers; to ProofScript, an array of
// length exactly n, and a number below n.
export type Vec<T, n extends nat> = readonly T[] & Length<n>;
export type Fin<n extends nat> = nat & Lt<n>;

// Dependent return type: `typeof n` is the value n itself.
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

// `n` is never passed: it is determined by `xs` (n = xs.length), and `ys` must match it.
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

// No bounds check needed in the body: `i < n === xs.length` is part of the types.
export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T {
  return xs[i];
}

// Callers: lengths and indices are checked at every call.
export function third(): nat {
  return get([10, 20, 30], 2);
}

export function pairs(): Vec<[nat, boolean], 2> {
  return zip(replicate(2, 7), [true, false]);
}

// A theorem about value-indexed arrays: the refinement is a hypothesis.
export function vec_nonempty<n extends nat>(xs: Vec<nat, n>, i: Fin<n>): Proof {
  return prove(xs.length > 0, omega);
}
