import { omega, prove, type nat, type Proof } from "proofscript";

export function good(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

// False: must fail without stopping `good` from being verified.
export function bad(a: nat): Proof {
  return prove(a + 1 === a, omega);
}
