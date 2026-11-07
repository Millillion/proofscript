# Getting started with ProofScript

ProofScript is TypeScript with proofs. Your files stay `.ts`: `tsc`, your editor and your bundler see ordinary TypeScript. `proofscript check` proves the theorems and specifications in them, and ProofScript's kernel checks every proof.

This tutorial is a real project: [`examples/tutorial`](../examples/tutorial). Every line below is checked by the test suite.

## Setup

ProofScript is not on npm yet (that comes with 0.1.0). For now, work in a clone:

```bash
git clone https://github.com/Millillion/proofscript.git
```

```bash
cd proofscript && npm install
```

You need Node 24 or later. To **prove** (not only to check certificates), you also need Lean's installer, [elan](https://lean-lang.org/install). ProofScript installs the exact Lean version it needs, and builds lean4export, the first time it runs.

Check the tutorial:

```bash
cd examples/tutorial && ../../packages/checker/bin/proofscript.mjs check
```

```
✓ add_comm (src/1-theorems.ts:5) — verified, axioms: Quot.sound, propext
…
12/12 theorems verified; 2775 declarations checked by the ProofScript kernel.
```

Your own project needs a `tsconfig.json` and `proofscript` as a dependency. Run `proofscript check` in its directory, or pass a tsconfig or files.

## 1. Theorems

A theorem is a function that returns `Proof`. Its body states a fact as an ordinary boolean expression with `prove`, and says how to prove it.

```ts
import { implies, omega, prove, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

export function lt_of_lt_of_le(a: nat, b: nat, c: nat): Proof {
  return prove(implies(a < b && b <= c, a < c), omega);
}
```

- **Parameters** are universally quantified: `add_comm` holds for all `a` and `b`.
- **`nat`** is a non-negative safe integer. To `tsc` it is `number`. ProofScript never treats plain `number` as an integer, because it is IEEE-754 floating point.
- **Proofs are Lean's tactics**, with the same names and the same behaviour: `omega` decides linear arithmetic over the integers.
- **Calling a theorem runs its statement.** `add_comm(2, 3)` returns normally, and a false statement throws, so theorems double as property tests.

A false theorem fails, with Lean's explanation:

```
src/1-theorems.ts:5:1: error: proof failed: omega could not prove the goal: …
✗ add_comm (src/1-theorems.ts:5) — failed
```

### Induction, and exact numbers

```ts
// `nat` is a JavaScript number: n + sum_to(n - 1) could pass 2^53 and lose precision,
// and ProofScript would reject it. `Nat` (a bigint) is exact, for mathematics.
export function sum_to(n: Nat): Nat {
  return n === 0n ? 0n : n + sum_to(n - 1n);
}

export function gauss(n: Nat): Proof {
  return prove(
    2n * sum_to(n) === n * (n + 1n),
    by(induction(n, {
      zero: () => simp_all(sum_to),
      succ: (_k, _ih) => by(unfold(sum_to), grind),
    })),
  );
}
```

- **Arithmetic on `nat` must stay exact.** ProofScript proves that runtime arithmetic on `nat` and `int` stays below 2⁵³. Try `sum_to` on `nat`: it is rejected, because large inputs would overflow. `Nat` and `Int` are bigints, which are exact.
- **`induction(n, { zero, succ })`** is Lean's `induction n with | zero => … | succ k ih => …`. The callback parameters name the constructor's fields and the induction hypothesis.
- **`by(t1, t2, …)`** runs tactics in sequence. `unfold(f)` unfolds a definition once. `grind` combines congruence closure, ring arithmetic and case splits.

## 2. Specifications on ordinary functions

Refinement types are intersections that TypeScript ignores and ProofScript proves. To `tsc`, `Ge<1>` is `unknown`, so `nat & Ge<1>` is just `number`.

```ts
import type { Ge, Le, Lt, nat } from "proofscript";

// A precondition (n >= 1) and a postcondition (the result is below n).
export function pred(n: nat & Ge<1>): nat & Lt<typeof n> {
  return n - 1;
}

export function predOrZero(n: nat): nat {
  return n >= 1 ? pred(n) : 0;
}

export function clamp(x: nat, hi: nat): nat & Le<typeof hi> & Le<typeof x> {
  return x <= hi ? x : hi;
}
```

- **Postconditions** (refined return types) are proved automatically, by unfolding, arithmetic and induction. Each becomes a reported theorem: `pred (postcondition Lt<typeof n>)`.
- **Preconditions** (refined parameters) are assumed inside the function, and must be proved at every call. In `predOrZero`, the branch condition proves `n >= 1`. A call such as `pred(0)` is rejected: `a precondition may not hold at a call in …`.
- **`typeof n`** in a type means the *value* of `n`.
- **`n - 1` on `nat`** is allowed only where it cannot go below zero. Lean's natural-number subtraction would silently truncate; JavaScript's would go negative.

## 3. Data types and induction

A discriminated union is an inductive data type. Functions over it are definitions in the logic.

```ts
export type List<T> = { readonly tag: "nil" } | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function append<T>(xs: List<T>, ys: List<T>): List<T> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

export function length_append<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs, {
      nil: () => simp(length, append),
      cons: (_head, _tail, ih) => by(simp(length, append, ih), omega),
    })),
  );
}
```

- **`simp(f, g, lemma)`** is Lean's `simp [f, g, lemma]`: it rewrites with definitions and lemmas.
- **The `1 + length(tail)` overflow check** is discharged by a stated assumption. A count produced by recursion is bounded by the recursion depth, and JavaScript's stack overflows long before 2³⁰ frames. The result lists it: `assumes recursion depth below 2^30`.
- **Plain object types and interfaces** are structures. **Strings** are sequences of UTF-16 code units, as in JavaScript.

## 4. Loops

`x satisfies R;` at the top of a loop body is a loop invariant, and `e satisfies Decreases;` is a termination measure. Both are ordinary TypeScript.

```ts
export function countBelow(a: readonly nat[], limit: nat): nat & Le<typeof a.length> {
  let c = 0;
  for (let i = 0; i < a.length; i++) {
    i satisfies Le<typeof a.length>;
    c satisfies Le<typeof i>;
    a.length - i satisfies Decreases;
    if (a[i] < limit) c = c + 1;
  }
  return c;
}
```

- **Invariants** are proved on entry to the loop and after every iteration, and assumed in the body. Here `c ≤ i` carries the postcondition: when the loop exits, `i = a.length`.
- **`a[i]` must be in bounds.** In JavaScript, an out-of-bounds read is `undefined`. Here `i < a.length` comes from the loop condition.
- **Termination:** the measure must decrease on every iteration and stay non-negative.

## 5. Mutation

Arrays and objects can be changed in place. `Modifies<typeof a>` declares what a function may change, and `Old<typeof a>` is the value on entry.

```ts
export function swap(
  a: nat[],
  i: nat & Lt<typeof a.length>,
  j: nat & Lt<typeof a.length>,
): void & Modifies<typeof a> & Holds<typeof swapped, [typeof a, Old<typeof a>, typeof i, typeof j]> {
  const t = a[i];
  a[i] = a[j];
  a[j] = t;
}
```

- **`Holds<typeof p, [args…]>`** states that the predicate `p(args…)` holds after the call. `swapped` is an ordinary boolean function; see [`5-mutation.ts`](../examples/tutorial/src/5-mutation.ts).
- **Writes are proved in bounds.** `push` is proved to keep the length below 2³².
- **Aliasing is not allowed** (`const b = a`, or passing the same array twice). Exported modifying functions list the assumption that their callers don't alias arguments either.

## 6. Checking without Lean: certificates

```bash
proofscript check --write-certificate    # prove with Lean; save proofscript.cert
proofscript check --certificate          # check against it, with Node only
```

Commit `proofscript.cert`, and CI can check every proof without installing Lean. A certificate is not trusted. Every proof in it is re-checked by the kernel, and every statement is matched against your current TypeScript. If you edit a theorem's statement, that theorem needs Lean again. See [certificates](certificates.md).

## 7. What do my results rest on? `proofscript audit`

```bash
proofscript audit --certificate
```

```
Theorems: 12 (12 verified, 0 admitted, 0 not verified)

Axioms
  propext (standard) — 12 theorems: …
Trusted translations (TypeScript functions reflected into the logic)
  append — 1 theorem: length_append
Assumptions
  recursion depth below 2^30 — 1 theorem: length_append
Boundary (where verified code meets unverified code)
  src/2-specs.ts:6:1: pred is exported: callers outside this project must establish its preconditions themselves
…
```

- **Axioms:** Lean's three standard axioms are expected. `sorry` means a proof was left out (the result is *admitted*).
- **Trusted translations:** the TypeScript functions a result reasons about. ProofScript trusts that its translation of them means what JavaScript does.
- **Assumptions:** facts about the runtime environment that proofs rely on.
- **Boundary:** places where unverified code (or code outside the project) calls a function whose preconditions nothing proves. `--json` prints the audit for tools.

## Next

- [Reference](reference.md): every ProofScript type, function and tactic, and the TypeScript the logic supports.
- [`examples/math`](../examples/math): a library with lists, insertion sort, an inductive family of propositions, and value-indexed vectors.
