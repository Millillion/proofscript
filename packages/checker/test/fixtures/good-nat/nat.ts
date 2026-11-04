import { by, implies, omega, prove, unfold, type Lt, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

// n + n must stay below 2^53 in JavaScript, so `double` requires n < 2^52.
export function double(n: nat & Lt<4503599627370496>): nat {
  return n + n;
}

export function double_ge(n: nat): Proof {
  return prove(implies(n < 4503599627370496, double(n) >= n), by(unfold(double), omega));
}
