import type { Ge, nat } from "proofscript";

export function pred(n: nat & Ge<1>): nat {
  return n - 1;
}

// No spec of its own, but it calls `pred`: its call must satisfy pred's precondition.
export function bad(): nat {
  return pred(0);
}
