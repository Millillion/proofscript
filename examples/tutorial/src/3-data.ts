// Step 3: data types. A discriminated union is an inductive type; recursive functions
// over it can be used in theorems, and proved about by induction.
import { by, induction, omega, prove, simp, type nat, type Proof } from "proofscript";

export type List<T> = { readonly tag: "nil" } | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function append<T>(xs: List<T>, ys: List<T>): List<T> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

// The callback parameters name the constructor's fields and the induction hypothesis.
export function length_append<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs, {
      nil: () => simp(length, append),
      cons: (_head, _tail, ih) => by(simp(length, append, ih), omega),
    })),
  );
}
