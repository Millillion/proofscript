import type { Is, nat } from "proofscript";

export type List =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: nat; readonly tail: List };

export function length(xs: List): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function sameLength(r: List, xs: List, _ys: List): boolean {
  return length(r) === length(xs);
}

// Wrong postcondition: appending changes the length. Must not verify.
export function append(xs: List, ys: List): List & Is<typeof sameLength, [typeof xs, typeof ys]> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}
