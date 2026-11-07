import { forall, implies, type Decreases, type Holds, type Le, type Modifies, type nat } from "proofscript";

export function f(p: nat): nat {
  return (p % 64) * 7 % 64;
}

export function filledUpTo(out: readonly nat[], j: nat): boolean {
  return forall((p: nat) => implies(p < j && p < out.length, out[p] === f(p)));
}

// Off by one: the last element is never written, yet the invariant claims it.
export function fillWrong(out: nat[]): void & Modifies<typeof out> & Holds<typeof filledUpTo, [typeof out, typeof out.length]> {
  let j = 0;
  while (j + 1 < out.length) {
    j satisfies Le<typeof out.length>;
    out satisfies Holds<typeof filledUpTo, [typeof out, typeof j]>;
    out.length - j satisfies Decreases;
    out[j] = f(j);
    j = j + 1;
  }
}

// A specification predicate cannot run: in JavaScript it would always return true.
export function check(out: readonly nat[]): nat {
  return filledUpTo(out, 3) ? 1 : 0;
}
