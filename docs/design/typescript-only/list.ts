import { by, induction, prove, simp, type Is, type nat, type Proof, type Simp } from "./proofscript/index.ts";

export type List<T> =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

// A postcondition is a refinement of the return type, using an ordinary predicate.
const appendLength = <T>(r: List<T>, xs: List<T>, ys: List<T>) => length(r) === length(xs) + length(ys);

export function append<T>(xs: List<T>, ys: List<T>): List<T> & Is<typeof appendLength, [typeof xs, typeof ys]> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

export function fromArray<T>(a: readonly T[]): List<T> {
  let r: List<T> = { tag: "nil" };
  for (let i = a.length - 1; i >= 0; i--) r = { tag: "cons", head: a[i], tail: r };
  return r;
}

// Theorems can sit right next to the code they are about, as in Lean.
// `Proof & Simp` is Lean's `@[simp] theorem`.
export function length_append<T>(xs: List<T>, ys: List<T>): Proof & Simp {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs), simp(length, append)),
  );
}
