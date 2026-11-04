// Insertion sort, proved to produce a sorted permutation of its input.
import { andThen, by, grind, implies, induction, intro, omega, prove, simp, simp_all, simp_only, split, type nat, type Proof } from "proofscript";
import { length, type List } from "./list.ts";

/** Every element of xs is at least x. */
export function allGe(x: nat, xs: List<nat>): boolean {
  return xs.tag === "nil" ? true : x <= xs.head && allGe(x, xs.tail);
}

export function sorted(xs: List<nat>): boolean {
  return xs.tag === "nil" ? true : allGe(xs.head, xs.tail) && sorted(xs.tail);
}

export function insert(x: nat, xs: List<nat>): List<nat> {
  if (xs.tag === "nil") return { tag: "cons", head: x, tail: xs };
  if (x <= xs.head) return { tag: "cons", head: x, tail: xs };
  return { tag: "cons", head: xs.head, tail: insert(x, xs.tail) };
}

export function sort(xs: List<nat>): List<nat> {
  return xs.tag === "nil" ? xs : insert(xs.head, sort(xs.tail));
}

/** How many times y occurs in xs. */
export function count(y: nat, xs: List<nat>): nat {
  if (xs.tag === "nil") return 0;
  return xs.head === y ? 1 + count(y, xs.tail) : count(y, xs.tail);
}

export function allGe_insert(y: nat, x: nat, xs: List<nat>): Proof {
  return prove(
    implies(y <= x && allGe(y, xs), allGe(y, insert(x, xs))),
    by(induction(xs, {
      nil: () => simp_all(insert, allGe),
      // `insert` branches on x <= head: split the cases, then simplify and do arithmetic.
      cons: (_h, _t, _ih) => by(intro("hyp"), simp_only(insert), andThen(split, simp_all(allGe), omega)),
    })),
  );
}

export function allGe_weaken(y: nat, z: nat, xs: List<nat>): Proof {
  return prove(
    implies(z <= y && allGe(y, xs), allGe(z, xs)),
    by(induction(xs, {
      nil: () => simp(allGe),
      cons: (_h, _t, _ih) => by(simp_all(allGe), omega),
    })),
  );
}

export function insert_sorted(x: nat, xs: List<nat>): Proof {
  return prove(
    implies(sorted(xs), sorted(insert(x, xs))),
    by(induction(xs, {
      nil: () => simp(insert, sorted, allGe),
      cons: (_h, _t, _ih) =>
        by(intro("hyp"), simp_only(insert), andThen(split, simp_all(sorted, allGe), grind(allGe_insert, allGe_weaken))),
    })),
  );
}

export function sort_sorted(xs: List<nat>): Proof {
  return prove(
    sorted(sort(xs)),
    by(induction(xs, {
      nil: () => simp(sort, sorted),
      cons: (_h, _t, _ih) => simp_all(sort, insert_sorted),
    })),
  );
}

export function count_insert(y: nat, x: nat, xs: List<nat>): Proof {
  return prove(
    count(y, insert(x, xs)) === (x === y ? 1 : 0) + count(y, xs),
    by(induction(xs, {
      nil: () => simp(insert, count),
      cons: (_h, _t, _ih) => by(simp_only(insert), andThen(split, simp_all(count), grind)),
    })),
  );
}

// sort(xs) has exactly the same elements as xs, with the same multiplicities.
export function sort_permutation(y: nat, xs: List<nat>): Proof {
  return prove(
    count(y, sort(xs)) === count(y, xs),
    by(induction(xs, {
      nil: () => simp(sort, count),
      cons: (_h, _t, _ih) => by(simp_all(sort, count, count_insert), grind),
    })),
  );
}

export function length_insert(x: nat, xs: List<nat>): Proof {
  return prove(
    length(insert(x, xs)) === 1 + length(xs),
    by(induction(xs, {
      nil: () => simp(insert, length),
      cons: (_h, _t, _ih) => by(simp_only(insert), andThen(split, simp_all(length), omega)),
    })),
  );
}

export function length_sort(xs: List<nat>): Proof {
  return prove(
    length(sort(xs)) === length(xs),
    by(induction(xs, {
      nil: () => simp(sort),
      cons: (_h, _t, _ih) => simp_all(sort, length, length_insert),
    })),
  );
}
