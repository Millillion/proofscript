import { congrArg, omega, prove, rfl, simp, by, type nat, type Proof } from "./proofscript/index.ts";
import { append, length, length_append, type List } from "./list.ts";

// Theorems can also live in their own module. This one uses `length_append`
// from list.ts as a simp lemma.
export function length_append_comm<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(append(ys, xs)),
    by(simp(length_append), omega),
  );
}

// A term proof of the same fact as list.ts's `length_append`: induction is recursion.
export function length_append_term<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(length(append(xs, ys)) === length(xs) + length(ys), () =>
    xs.tag === "nil"
      ? rfl
      : congrArg((n: nat) => 1 + n, length_append_term(xs.tail, ys)));
}
