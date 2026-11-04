// Immutable lists and the classic theorems about them.
import { by, eq, induction, omega, prove, simp, simp_all, type nat, type Proof, type Simp } from "proofscript";

export type List<T> =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function append<T>(xs: List<T>, ys: List<T>): List<T> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

export function reverse<T>(xs: List<T>): List<T> {
  return xs.tag === "nil" ? xs : append(reverse(xs.tail), { tag: "cons", head: xs.head, tail: { tag: "nil" } });
}

export function length_append<T>(xs: List<T>, ys: List<T>): Proof & Simp {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs, {
      nil: () => simp(length, append),
      cons: (_h, _t, ih) => by(simp(length, append, ih), omega),
    })),
  );
}

export function append_nil<T>(xs: List<T>): Proof & Simp {
  return prove(
    eq(append(xs, { tag: "nil" }), xs),
    by(induction(xs, {
      nil: () => simp(append),
      cons: (_h, _t, ih) => simp(append, ih),
    })),
  );
}

export function append_assoc<T>(xs: List<T>, ys: List<T>, zs: List<T>): Proof & Simp {
  return prove(
    eq(append(append(xs, ys), zs), append(xs, append(ys, zs))),
    by(induction(xs, {
      nil: () => simp(append),
      cons: (_h, _t, ih) => simp(append, ih),
    })),
  );
}

export function reverse_append<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    eq(reverse(append(xs, ys)), append(reverse(ys), reverse(xs))),
    by(induction(xs, {
      nil: () => simp(reverse, append, append_nil),
      cons: (_h, _t, ih) => simp(reverse, append, ih, append_assoc),
    })),
  );
}

export function reverse_reverse<T>(xs: List<T>): Proof {
  return prove(
    eq(reverse(reverse(xs)), xs),
    by(induction(xs, {
      nil: () => simp(reverse),
      cons: (_h, _t, ih) => simp_all(reverse, reverse_append, append),
    })),
  );
}

export function length_reverse<T>(xs: List<T>): Proof {
  return prove(
    length(reverse(xs)) === length(xs),
    by(induction(xs, {
      nil: () => simp(reverse),
      cons: (_h, _t, ih) => by(simp(reverse, length, ih), omega),
    })),
  );
}
