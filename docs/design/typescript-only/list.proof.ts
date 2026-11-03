import { congrArg, eq, omega, prove, rfl, rw, by, type Proof } from "./proofscript/index.ts";
import { append, length, length_append, type List } from "./list.ts";

// Theorems can also live in their own module. This one rewrites with
// `length_append` from list.ts, then finishes with linear arithmetic.
export function length_append_comm<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(append(ys, xs)),
    by(rw(length_append, length_append), omega),
  );
}

// A term proof: induction is recursion, case analysis is `?:`.
// `eq` is structural equality (`===` on objects would compare identity).
export function append_nil<T>(xs: List<T>): Proof {
  return prove(eq(append(xs, { tag: "nil" }), xs), () =>
    xs.tag === "nil"
      ? rfl
      : congrArg((r: List<T>): List<T> => ({ tag: "cons", head: xs.head, tail: r }), append_nil(xs.tail)));
}
