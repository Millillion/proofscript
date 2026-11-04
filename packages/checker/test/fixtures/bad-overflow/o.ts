import type { Ge, nat } from "proofscript";

// n * n overflows 2^53 for large n (JavaScript would silently round). Must not verify.
export function square(n: nat): nat & Ge<0> {
  return n * n;
}
