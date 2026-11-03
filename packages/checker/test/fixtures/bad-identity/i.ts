import { implies, prove, rfl, type Proof } from "proofscript";

export type Box = { readonly tag: "box"; readonly x: boolean };

// `===` on objects compares identity in JavaScript: two boxes with equal
// contents need not be ===. tsc accepts this; ProofScript must not treat it as
// structural equality.
export function boxes_equal(a: Box, b: Box): Proof {
  return prove(implies(a.x === b.x, a === b), rfl);
}
