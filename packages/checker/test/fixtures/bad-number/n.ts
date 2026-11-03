import { omega, prove, type Proof } from "proofscript";

// `number` is IEEE-754: 0.1 + 0.2 !== 0.3, and (a + b) + c !== a + (b + c) in general.
export function float_assoc(a: number, b: number, c: number): Proof {
  return prove(a + b + c === a + (b + c), omega);
}
