import type { Ge, nat } from "proofscript";

export function pred(n: nat & Ge<1>): nat {
  return n - 1;
}

// A verified caller: the precondition is proved at the call.
export function two(): nat {
  return pred(3);
}

// Outside the logic (floating-point `number`): the call cannot be checked, and is reported.
export function fromFloat(x: number): nat {
  return pred(Math.round(x));
}
