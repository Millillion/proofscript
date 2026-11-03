# Surface Syntax: ProofScript Is Written in TypeScript

Status: **design note v0.2** (2026-11-02). Supersedes the concrete syntax in [02-language-design.md §7](02-language-design.md#7-concrete-syntax) and v0.1 of this note (which used `//@` comment annotations).

Decisions recorded:
- **Kernel:** our own Lean-4-compatible kernel in TypeScript, re-checked by Lean in CI.
- **Surface:** the entire ProofScript type system is expressed in actual TypeScript: types, `satisfies`, and ordinary functions. No new syntax, and no comments carrying meaning.

## 1. Is it basically Lean's type system?

**The kernel is exactly Lean 4's type theory**: dependent functions, a universe hierarchy, inductive families, an impredicative proof-irrelevant `Prop`, quotients, and the same axioms. It is well understood, consistent relative to ZFC with inaccessible cardinals (Carneiro, 2019), has several independent checkers, and lets proofs be exported to Lean for re-checking.

**The surface is TypeScript.** The checker interprets TypeScript types into the kernel (discriminated unions become inductive types, `number` becomes IEEE-754 binary64, `T & R` becomes a refinement, and so on). Universes and implicit arguments are inferred. JavaScript keeps its real semantics: `number` is a float, `===` is JavaScript's `===`, and `int`/`nat` are proved refinements.

## 2. What `tsc` checks, and what it can't

Neither the dedicated `.pts` syntax of design §7 nor any other design gets `tsc` to verify ProofScript's *meaning*. That is always the ProofScript checker's job. What differs is how much of the *surface* `tsc` sees:

- **Dedicated `.pts` syntax:** `tsc` cannot even parse it. It would see only a generated "virtual TS" view, produced by ProofScript's own tooling through the TS 7.1 content-mapper or Volar plumbing, in which spec expressions are copied into dead code so that their names and types get checked. That checking is real, but it is indirect and depends on our tooling.
- **Comment annotations (v0.1 of this note):** `tsc` sees nothing inside them.
- **TypeScript-only (this note):** `tsc` checks everything natively, with no plumbing.
  - Predicates are real functions, so their bodies are fully type-checked.
  - Spec plumbing is type-checked too. `Is<typeof found, [typeof a, typeof key]>` is a `tsc` error if `found` doesn't accept those arguments.
  - Rename, go-to-definition and find-references work across code and specs in every editor today.

## 3. The constraint that shapes the design

TypeScript's grammar has two worlds: **types**, which are erased, and **expressions**, which run. No position in TypeScript holds an arbitrary expression *and* is erased.

The bridges between the worlds are few:

- **`typeof x` and `typeof x.y`**, which refer to values from inside types;
- **`satisfies`**, which attaches a type to an expression and erases to the bare expression;
- **literal types**, which are already singleton types (`3`, `"nil"`).

The design uses exactly these three. Specs are types. The predicates inside specs are ordinary TypeScript functions, referred to with `typeof`. Ghost statements are `satisfies` statements. Proofs are ordinary code in proof modules, which ship nowhere.

## 4. The design

### 4.1 Refinements, preconditions, postconditions: `T & R`

A refinement is an intersection. Every refinement type `R` from the `proofscript` package is `unknown` to TypeScript, so `T & R` is just `T` to `tsc`. To ProofScript, `T & R` is `{ x: T // R holds of x }`.

```ts
import type { Is, Le, Length, Lt, int, nat } from "proofscript";

export function isSorted(a: readonly int[]): boolean {            // an ordinary, executable predicate
  return a.every((x, i) => i === 0 || a[i - 1] <= x);
}
export type Sorted = readonly int[] & Is<typeof isSorted>;          // refinement by a predicate

export type Vec<T, n extends nat> = readonly T[] & Length<n>;       // value-indexed type

export function get<T>(xs: readonly T[], i: nat & Lt<typeof xs.length>): T {  // relational precondition
  return xs[i];
}
```

- **A refined parameter type is a precondition**, and **a refined return type is a postcondition** (Liquid Types' insight, in TypeScript's syntax):

  ```ts
  const found = (r: int, a: readonly int[], key: int) => (r >= 0 ? a[r] === key : !a.includes(key));

  export function binarySearch(a: Sorted, key: int): int & Is<typeof found, [typeof a, typeof key]> { … }
  ```

- Built-in refinements cover common facts (`Lt`, `Le`, `Gt`, `Ge`, `Length`). Anything else is `Is<typeof pred, Args>` with an ordinary TS predicate. Predicates are real code, so they are also usable as runtime checks and in tests.
- **Bounded quantifiers are just `every`/`some`.** ProofScript reflects `Array.prototype.every` with its real semantics, so `a.every((x, i) => …)` *is* "∀ i < a.length". Unbounded quantifiers (`forall`) are needed only in proof modules.

### 4.2 Value indices: `typeof x` and literal types

- A type parameter `n extends nat` ranges over numeric literal types. Literal types *are* singletons, so ProofScript reads `n` as a ghost value parameter.
- `typeof x` in an index or refinement position means "exactly the value `x`". TypeScript already does this when it can (`const n = 3` gives `typeof n` = `3`); ProofScript does it for every `x`.

Both readings *refine* TypeScript's own rather than reinterpret it.

```ts
export function replicate<T>(n: nat, x: T): Vec<T, typeof n> { … }      // depends on a runtime argument
export function zip<A, B, n extends nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> { … }
```

Arithmetic on indices uses type operators: `Vec<T, Plus<n, 1>>`.

### 4.3 Ghost statements: `satisfies`

`e satisfies R;` as a statement is an **assertion**: the checker must prove `R` holds of `e` here. At the top of a loop body it is a **loop invariant**. `e satisfies Decreases` there is the **termination measure**. TypeScript type stripping erases each one to a bare expression statement (`lo;`), which has no effect.

```ts
export function binarySearch(a: Sorted, key: int): int & Is<typeof found, [typeof a, typeof key]> {
  let lo = 0, hi = a.length;
  while (lo < hi) {
    lo satisfies nat & Le<typeof hi>;                                         // invariant
    hi satisfies nat & Le<typeof a.length>;                                   // invariant
    key satisfies Is<typeof notInOuter, [typeof a, typeof lo, typeof hi]>;    // invariant
    hi - lo satisfies Decreases;                                              // termination measure
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
```

Node's type stripping produces this (whitespace kept, so stack traces keep their positions):

```js
  while (lo < hi) {
    lo                              ;
    hi                                    ;
    key                                                                  ;
    hi - lo                    ;
    const mid = lo + Math.floor((hi - lo) / 2);
```

`null satisfies Use<typeof lemma, [typeof a, typeof i]>` instantiates a lemma at a point in the code, to give the checker a fact it can't find on its own.

Rules: the subject of a `satisfies` statement must be a local variable, a literal, or arithmetic on them, so that erasure leaves no observable effect (no property reads, which could run getters). A linter preset will mark these statements as intentional for `no-unused-expressions`.

### 4.4 Theorems: proof modules

Proofs live in `*.proof.ts` files, the way tests live in `*.test.ts`. They are type-checked with the project, never imported by production code, and never shipped. They import the inert runtime part of the `proofscript` package (a dev dependency, like a test framework).

```ts
import { by, congrArg, induction, prove, rfl, simp, type nat, type Proof } from "proofscript";
import { append, length, type List } from "./list.ts";

// A theorem is a function: parameters are universally quantified,
// and `prove` states the claim as an ordinary boolean expression.
export function length_append<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(
    length(append(xs, ys)) === length(xs) + length(ys),
    by(induction(xs), simp(length, append)),
  );
}

// The same theorem as a term proof: induction is recursion.
export function length_append_term<T>(xs: List<T>, ys: List<T>): Proof {
  return prove(length(append(xs, ys)) === length(xs) + length(ys), () =>
    xs.tag === "nil"
      ? rfl
      : congrArg((n: nat) => 1 + n, length_append_term(xs.tail, ys)));
}
```

Run as plain TypeScript, a theorem is a **property test**: `length_append(a, b)` evaluates the statement on those inputs and throws if it's false. ProofScript proves it for all inputs.

### 4.5 Inductive propositions: Curry–Howard in TypeScript types

```ts
import { by, exact, induction, simp, type nat, type Plus, type Prop } from "proofscript";

// inductive Even : Nat → Prop | zero : Even 0 | step : Even k → Even (k + 2)
export interface Even<n extends nat> extends Prop { readonly __index: n }
export declare namespace Even {
  function zero(): Even<0>;
  function step<k extends nat>(h: Even<k>): Even<Plus<k, 2>>;
}

// When the claim is a type, it is the return type.
export function even_add<a extends nat, b extends nat>(ha: Even<a>, hb: Even<b>): Even<Plus<a, b>> {
  return by(induction(ha, {
    zero: () => exact(hb),
    step: (_h, ih) => by(simp(), exact(Even.step(ih))),
  }));
}
```

`interface` and `declare namespace` emit no JavaScript. Tactics that introduce hypotheses take callbacks whose parameters name them, so every name in a proof is an ordinary TypeScript binding.

## 5. Verified prototype

[`typescript-only/`](typescript-only/) contains every example above as real files.

- **`tsc` 5.9 reports zero errors** with `strict`, `noUnusedLocals`, `noUnusedParameters`, `erasableSyntaxOnly` and `verbatimModuleSyntax` on.
- **`node main.ts` runs the files directly** under Node 24's built-in type stripping, with no loader and no build step.
- The only comments in the code are explanatory prose. None of them carries meaning.
- `main.ts` ends with two calls that `tsc` accepts and that run, but that ProofScript rejects:
  - `zip([1, 2, 3], ["x"])`: the lengths differ. It produces `[[1,"x"],[2,null],[3,null]]` (JSON prints the `undefined`s as `null`).
  - `get([10, 20, 30], 3)`: `3 < 3` is false. It returns `undefined` where TS promised a `number`.

## 6. The refinement principle

**The ProofScript meaning of every type is a subset of its TypeScript meaning.** So:

- `tsc` accepts every ProofScript program, and its checking remains valid, just weaker.
- Every ProofScript program is a TypeScript program, with no syntax added. This is the strongest possible form of the superset requirement (R1–R3).
- Implementation modules import ProofScript with `import type` only, so there is no runtime dependency (R6). Ghost statements erase to no-ops (R4).
- Every tool works unchanged: `tsc`, Node, Deno, Bun, Vite, esbuild, webpack, Prettier, ESLint, Biome, test runners, coverage, GitHub highlighting.
- No parser to fork, no loader, no dependence on the TypeScript 7.1 beta API.
- The ProofScript checker recognizes its types by **symbol resolution** (they must resolve to the `proofscript` package), never by name, so user types named `Is` or `Le` are never misread.

## 7. Costs, honestly

| Cost | Mitigation |
|---|---|
| Spec predicates must be **named functions**, since a type can't contain an inline expression. | Named predicates are reusable, testable and usable as runtime validators. Built-in refinements (`Lt`, `Length`, …) cover simple facts with no function at all. |
| Postconditions are verbose: `int & Is<typeof found, [typeof a, typeof key]>`. | A shorter form where the predicate receives the function's parameters implicitly (`Ensures<typeof found>`) is possible; `tsc` then can't check the argument list, but ProofScript does. |
| Index arithmetic: `Plus<n, 1>` instead of `n + 1`. | Rarely needed outside theorem-heavy code; refinements cover most program verification. |
| `x satisfies R;` statements are unusual. | They are short, real TypeScript and erase to nothing. A lint preset handles `no-unused-expressions`. |
| Module-level predicates referenced only via `typeof` remain in the emitted JS (a few small functions per module). | Put them in a companion module and import them with `import type` to emit nothing. Most bundlers tree-shake them anyway. |
| To `tsc`, `Sorted` is just `readonly int[]`, so `tsc` never forces you through `isSorted`. | Deliberate: ProofScript does that checking, without casts. Proofs never trust `as` casts (R17). |

## 8. File extensions

The question dissolves: implementation code stays `.ts` / `.tsx` / `.mts` / `.cts` (or `.js` with JSDoc types), and proofs go in `*.proof.ts`, mirroring `*.test.ts`. A double extension is safe precisely because the files are valid TypeScript.

## 9. Open questions

1. **Postcondition shorthand.** Explicit `Is<typeof post, [typeof a, typeof key]>` (fully `tsc`-checked) vs. implicit `Ensures<typeof post>` (shorter).
2. **Theorem statements.** `prove(boolean, proof)` (statement as an expression, runnable as a property test) vs. propositions as types throughout (`Eq<…>`, `And<…>`), which is more uniform with §4.5 but harder to read.
3. **Frames and mutation.** How `reads`/`modifies`/`old(e)` are expressed as types, e.g. `Modifies<typeof a>` on the return type and `Old<typeof x>` in predicates.
4. **Equality, numbers, termination and trust footprints** carry over unchanged from design §4–§6. Only the syntax changed.
