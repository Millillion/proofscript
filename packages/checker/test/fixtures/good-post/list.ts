import type { Ge, Is, Lt, nat } from "proofscript";

export type List =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: nat; readonly tail: List };

export function length(xs: List): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function appendLength(r: List, xs: List, ys: List): boolean {
  return length(r) === length(xs) + length(ys);
}

// Postcondition: the result's length is the sum. Proved automatically
// (functional induction on `append`, then simplification and arithmetic).
export function append(xs: List, ys: List): List & Is<typeof appendLength, [typeof xs, typeof ys]> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

// A precondition (assumed while proving the postcondition): n > 0.
export function pred(n: nat & Ge<1>): nat & Lt<typeof n> {
  return n - 1;
}
