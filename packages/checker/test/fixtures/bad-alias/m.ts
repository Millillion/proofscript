import type { Lt, Modifies, nat } from "proofscript";

export function setFirst(a: nat[] & Lt<4294967295>, b: readonly nat[]): void & Modifies<typeof a> {
  if (a.length > 0 && b.length > 0) a[0] = b[0];
}

// Passing the same array twice to a function that modifies one of them: rejected.
export function f(a: nat[]): void & Modifies<typeof a> {
  setFirst(a, a);
}
