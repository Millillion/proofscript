import { prove, sorry, type nat, type Proof } from "proofscript";

export function later(a: nat): Proof {
  return prove(a * a >= a, sorry);
}
