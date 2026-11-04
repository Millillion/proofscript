import type { Ge, int, Le, Lt, nat } from "proofscript";

export type List = { readonly tag: "nil" } | { readonly tag: "cons"; readonly head: nat; readonly tail: List };

// Counting in recursion: exempt (bounded by recursion depth), listed as an assumption.
export function length(xs: List): nat & Ge<0> {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

// Bounded inputs: provably no overflow.
export function average(a: nat & Lt<4503599627370496>, b: nat & Lt<4503599627370496>): nat & Ge<0> {
  return a <= b ? a + Math.floor((b - a) / 2) : b + Math.floor((a - b) / 2);
}

export function negate(x: int & Ge<-1000> & Le<1000>): int & Le<1000> {
  return 0 - x;
}
