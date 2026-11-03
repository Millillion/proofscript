import { omega, prove, type nat, type Proof } from "proofscript";

// False: must not verify.
export function bogus(a: nat, b: nat): Proof {
  return prove(a + b === a, omega);
}
