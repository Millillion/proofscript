import type { Indexed, nat } from "./proofscript/index.ts";

// Refinement types: TypeScript sees the carrier, ProofScript sees the predicate.
//@ where xs => xs.length === n
export type Vec<T, n extends nat> = Indexed<readonly T[], n>;

//@ where i => i < n
export type Fin<n extends nat> = Indexed<nat, n>;

// Dependent return type: `typeof n` is `number` to TypeScript, and the
// singleton "exactly the value n" to ProofScript.
export function replicate<T>(n: nat, x: T): Vec<T, typeof n> {
  const out: T[] = [];
  for (let i = 0; i < n; i++) {
    //@ invariant out.length === i && i <= n
    out.push(x);
  }
  return out;
}

export function zip<A, B, n extends nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> {
  const out: [A, B][] = [];
  for (let i = 0; i < xs.length; i++) {
    //@ invariant out.length === i && i <= n
    out.push([xs[i], ys[i]]);
  }
  return out;
}

// No bounds check needed: `i < n === xs.length` is part of the types.
export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T {
  return xs[i];
}
