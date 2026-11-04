import type { Ge, Length, Lt, nat } from "proofscript";

export type Vec<T, n extends nat> = readonly T[] & Length<n>;
export type Fin<n extends nat> = nat & Lt<n>;

export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T {
  return xs[i];
}

// 3 is not below 3: rejected.
export function oops(): nat & Ge<0> {
  return get([10, 20, 30], 3);
}
