// Arithmetic on natural numbers. In theorems, `nat` arithmetic is exact.
import { grind, implies, omega, prove, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

export function add_assoc(a: nat, b: nat, c: nat): Proof {
  return prove(a + b + c === a + (b + c), omega);
}

export function mul_comm(a: nat, b: nat): Proof {
  return prove(a * b === b * a, grind);
}

export function left_distrib(a: nat, b: nat, c: nat): Proof {
  return prove(a * (b + c) === a * b + a * c, grind);
}

export function le_trans(a: nat, b: nat, c: nat): Proof {
  return prove(implies(a <= b && b <= c, a <= c), omega);
}

export function square_binomial(a: nat, b: nat): Proof {
  return prove((a + b) * (a + b) === a * a + 2 * a * b + b * b, grind);
}
