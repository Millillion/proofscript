import { by, omega, prove, unfold, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

export function double(n: nat): nat {
  return n + n;
}

export function double_ge(n: nat): Proof {
  return prove(double(n) >= n, by(unfold(double), omega));
}
