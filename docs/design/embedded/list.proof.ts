import { by, congrArg, induction, prove, rfl, simp, type nat, type Proof } from "./proofscript/index.ts";
import { append, length, type List } from "./list.ts";

// A theorem is a function: its parameters are universally quantified, and
// `prove` states the claim as an ordinary boolean expression.
export function length_append<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs), simp(length, append)),
  );
}

// The same theorem as a term proof: induction is recursion, case analysis is `?:`.
export function length_append_term<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(length(append(xs, ys)) === length(xs) + length(ys), () =>
    xs.tag === "nil"
      ? rfl
      : congrArg((n: nat) => 1 + n, length_append_term(xs.tail, ys)));
}
