// Step 2: specifications on ordinary functions. Refinement types are intersections
// that TypeScript ignores (`Ge<1>` is `unknown` to tsc) and ProofScript proves.
import type { Ge, Le, Lt, nat } from "proofscript";

// A precondition (n >= 1) and a postcondition (the result is below n).
export function pred(n: nat & Ge<1>): nat & Lt<typeof n> {
  return n - 1;
}

// Every call of `pred` must establish its precondition. Here it is proved from the
// branch condition; `pred(0)` would be rejected.
export function predOrZero(n: nat): nat {
  return n >= 1 ? pred(n) : 0;
}

// Several postconditions at once.
export function clamp(x: nat, hi: nat): nat & Le<typeof hi> & Le<typeof x> {
  return x <= hi ? x : hi;
}
