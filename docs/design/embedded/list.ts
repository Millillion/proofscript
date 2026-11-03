import type { nat } from "./proofscript/index.ts";

export type List<T> =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

//@ ensures r => length(r) === length(xs) + length(ys)
export function append<T>(xs: List<T>, ys: List<T>): List<T> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

export function fromArray<T>(a: readonly T[]): List<T> {
  let r: List<T> = { tag: "nil" };
  for (let i = a.length - 1; i >= 0; i--) r = { tag: "cons", head: a[i], tail: r };
  return r;
}
