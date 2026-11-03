# Surface Syntax: Dedicated Syntax vs. Valid TypeScript

Status: **design note v0.1** (2026-11-02). Follows up [02-language-design.md](02-language-design.md), which assumed a dedicated `.pts` grammar. This note asks whether ProofScript can instead be **valid TypeScript from day one**, with its meaning supplied by the ProofScript checker alone. It answers yes, and recommends making that the primary surface.

Decision recorded: **kernel = our own Lean-4-compatible kernel in TypeScript, re-checked by Lean in CI** (design §12, question 1).

## 1. Is it basically Lean's type system?

**The kernel is exactly Lean 4's type theory**: dependent functions, a universe hierarchy, inductive families, an impredicative proof-irrelevant `Prop`, quotients, and the same axioms. That is deliberate. It is well understood, proved consistent relative to ZFC with inaccessible cardinals (Carneiro, 2019), has several independent checkers, and lets proofs be exported to Lean for re-checking (and, later, Lean libraries be imported).

**The surface is not Lean.** Users write TypeScript types. The elaborator interprets them into the kernel (discriminated unions become inductive types, `number` becomes IEEE-754 binary64, and so on; design §4.1), and adds dependency where TypeScript has none (value indices, refinements, propositions). Universes, implicit arguments and most of what makes Lean intimidating are inferred and rarely seen. Other differences from Lean:

- **Honest JavaScript semantics**: `number` is a float, `===` is JavaScript's `===`; `int`/`nat` are proved refinements (design §6.3).
- **Modes and erasure** (exec/ghost/proof), because the code runs as JavaScript rather than through Lean's compiler.
- **No type classes at first** (design §12, question 3).
- **TypeScript's own type system keeps running unchanged** alongside, as an unsound but useful first check.

So: Lean's logic, TypeScript's types and syntax, JavaScript's runtime semantics.

## 2. The idea: types with a simple meaning to `tsc` and a precise meaning to ProofScript

Every ProofScript construct can be written as valid TypeScript whose TS meaning is a **sound over-approximation** of its ProofScript meaning:

| Written as | TypeScript sees | ProofScript sees |
|---|---|---|
| `nat` | `number` | `{ x: number // safe integer, x >= 0 }` |
| `Vec<T, n>` (alias of `readonly T[]` with a `//@ where`) | `readonly T[]` | arrays whose length is exactly `n` |
| `typeof n` in an index position | the type of `n` (`number`) | the singleton "exactly the value `n`" |
| `Even<k>` (an `interface` + `declare namespace`) | an opaque type | an inductive family of propositions |
| `Plus<k, 2>` | `number` | the value `k + 2` |
| `prove(stmt, proof)` returning `Proof` | a function returning an opaque value | the theorem "∀ parameters, `stmt`" |
| `//@ requires P` | a comment | a precondition |

The invariant behind the table is the **refinement principle**: *the ProofScript meaning of every type is a subset of its TypeScript meaning.* Consequences:

- Everything TypeScript checks remains a valid (weaker) check, so nothing ProofScript says contradicts `tsc`.
- TypeScript accepts every ProofScript program, because ProofScript only adds information TS ignores.
- Erasure is trivial. Annotations are comments, type-only constructs are erased by every TS tool, and implementation modules use `import type` only, so they have no runtime dependency on ProofScript (R4, R6).

`typeof n` deserves a note. TypeScript already gives `typeof n` a singleton type when it can: `const n = 3` has `typeof n` = `3`. ProofScript does the same thing for *every* `n`, which is precisely a dependent type. Likewise, a type parameter `n extends nat` ranges over numeric literal types in TS; literal types are singleton types, so ProofScript reads it as a ghost value parameter. These readings are refinements of TypeScript's own, not reinterpretations.

## 3. A working example in valid TypeScript

The files in [`embedded/`](embedded/) are real. Against stock TypeScript 5.9 with `strict`, `noUnusedLocals`, `noUnusedParameters`, `erasableSyntaxOnly` and `verbatimModuleSyntax`, `tsc` reports **zero errors**, and `node main.ts` runs them directly under Node 24's built-in type stripping, with no loader and no build step.

### 3.1 Implementation code with specs (`list.ts`, `search.ts`)

```ts
import type { int } from "proofscript";

//@ requires isSorted(a)
//@ ensures r => (r >= 0 ==> a[r] === key) && (r < 0 ==> !a.includes(key))
export function binarySearch(a: readonly int[], key: int): int {
  let lo = 0, hi = a.length;
  while (lo < hi) {
    //@ invariant 0 <= lo && lo <= hi && hi <= a.length
    //@ invariant forall((i: nat) => (i < lo || (hi <= i && i < a.length)) ==> a[i] !== key)
    //@ decreases hi - lo
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
```

### 3.2 Dependent and refinement types (`vec.ts`)

```ts
import type { Indexed, nat } from "proofscript";

//@ where xs => xs.length === n
export type Vec<T, n extends nat> = Indexed<readonly T[], n>;

//@ where i => i < n
export type Fin<n extends nat> = Indexed<nat, n>;

export function replicate<T>(n: nat, x: T): Vec<T, typeof n> { … }
export function zip<A, B, n extends nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> { … }
export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T { return xs[i]; }  // no bounds check needed
```

`zip([1, 2, 3], ["x"])` type-checks in TypeScript (to `tsc`, a `Vec` is just an array) and runs, producing `[[1,"x"],[2,null],[3,null]]` (JSON prints the `undefined`s as `null`). **ProofScript rejects that call**: no single `n` makes both arguments `Vec<_, n>`.

### 3.3 Theorems (`list.proof.ts`)

Proofs live in **proof modules**, `*.proof.ts`, the way tests live in `*.test.ts`: valid TypeScript, type-checked with the project, never imported by production code, so never shipped.

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

Because the statement is real TypeScript, `tsc` type-checks it, and rename and go-to-definition work on `length` and `append` inside theorems with no ProofScript plugin at all. As a bonus, **a theorem run as plain TS is a property test**: `length_append(someList, otherList)` evaluates the statement on those inputs and throws if it is false. ProofScript proves it for every input.

### 3.4 Inductive propositions (`even.proof.ts`)

```ts
import { by, exact, induction, simp, type nat, type Plus, type Prop } from "proofscript";

// inductive Even : Nat → Prop | zero : Even 0 | step : Even k → Even (k + 2)
export interface Even<n extends nat> extends Prop { readonly __index: n }
export declare namespace Even {
  function zero(): Even<0>;
  function step<k extends nat>(h: Even<k>): Even<Plus<k, 2>>;
}

// Curry–Howard: when the claim is a type, it is the return type.
export function even_add<a extends nat, b extends nat>(ha: Even<a>, hb: Even<b>): Even<Plus<a, b>> {
  return by(induction(ha, {
    zero: () => exact(hb),
    step: (_h, ih) => by(simp(), exact(Even.step(ih))),
  }));
}
```

Tactics that introduce hypotheses (Lean's `induction … with | step h ih => …`) take **callbacks whose parameters name the hypotheses**, so every name in a proof is an ordinary TypeScript binding.

## 4. Embedded-mode rules

1. **Annotations** are line comments `//@ <keyword> …` or block comments `/*@ <keyword> … */`, where `<keyword>` is from a closed set: `requires`, `ensures`, `decreases`, `reads`, `modifies`, `throws`, `invariant`, `assert`, `assume`, `ghost`, `proof`, `where`. Anything else after `//@` is ignored, so existing `//@ts-ignore`, `//@ts-expect-error` and legacy `//@ sourceMappingURL=` comments keep their meaning (R2). JSDoc tags are *not* used: JSDoc already defines `@requires` (a module dependency) and `@throws`, so reusing them would reinterpret existing comments.
2. **Spec expressions** inside annotations are TypeScript expressions plus `==>` and `<==>` (design §6.1). In proof modules, which are real code, `implies(p, q)` is the equivalent.
3. **The `proofscript` package** provides types (`nat`, `int`, `Indexed`, `Plus`, `Prop`, `Proof`, …) and inert runtime functions (`prove`, `by`, tactics, `forall`, …). The checker recognizes these by *symbol resolution* (they must resolve to the `proofscript` package), not by name, so a user's own function called `prove` is never misread.
4. **Implementation modules** import ProofScript only with `import type`. **Proof modules** (`*.proof.ts`) may import its runtime surface; they are dev-only, like test files.
5. **Ghost code in implementation modules** lives in annotations: `//@ ghost const before = total`, `//@ assert lo < hi`, `//@ proof lemma(a, i)`.
6. **Lemmas referenced only from annotations** are imported with an annotation, `//@ import { lemma } from "./x.proof.ts"`, so `noUnusedLocals` is not tripped and production code gains no import.

## 5. Trade-offs

| | Embedded (valid TS) | Dedicated syntax (`.pts`) |
|---|---|---|
| Works today with `tsc`, Node, Deno, Bun, Vite, esbuild, webpack | **Yes, demonstrated** | Needs a loader, plugins, and the TS 7.1 content-mapper or Volar integration |
| Prettier, ESLint, Biome, oxc, test runners, coverage, GitHub highlighting | **Unchanged** | Each needs ProofScript support (TypeScript needed years and Microsoft's weight to get this) |
| Parser to build and maintain | **None** (reuse TypeScript's) | A fork of TypeScript's parser, tracking every TS release |
| Superset property (R1–R3) | **Trivial**: no syntax is added at all | Must be engineered and tested (design §7.1) |
| Theorems and proofs | Real TS: type-checked, renameable, runnable as property tests | Real syntax: shortest form |
| Specs inside implementation code | Comments: TS does not check them; editor support comes from the ProofScript plugin | Syntax: TS-checked through the virtual TS view |
| Index arithmetic | `Vec<T, Plus<n, 1>>` | `Vec<T, n + 1>` |
| Reads like | TypeScript with annotations (Liquid Haskell, ACSL, JML, Python's typing) | A new language (Dafny, Verus, Lean) |

The embedded form costs some concision in theorem-heavy code and puts in-body specs in comments. In return it removes the largest engineering risks of the plan (parser fork, loader, dependence on the TS 7.1 beta API, ecosystem tooling) and makes adoption literally zero-cost: add a `//@ ensures` line to an existing `.ts` file and run `proofscript check`.

There is direct precedent in TypeScript's own history. TypeScript ships two surfaces over one checker: `.ts` syntax, and JSDoc annotations in plain `.js` files (`checkJs`). The JSDoc surface is what let many projects adopt types without a build step, and some (Svelte, in 2023) moved their own source to it.

## 6. Recommendation

1. **Make embedded mode the primary surface and build it first.** Every ProofScript program is a TypeScript program, with zero added syntax. This is the strongest possible form of the superset requirement.
2. **Keep the dedicated syntax as optional sugar for later**, designed as in design §7, desugaring to exactly the same core. Decide on it once embedded mode has real users and we know which parts are too noisy (theorem statements and index arithmetic are the likely candidates). Because both surfaces elaborate to the same kernel terms, adding it later is front-end work only.
3. **Front end**: use the TypeScript compiler's JavaScript API (6.x) for parsing and symbol resolution, which is free and exact. Like everything outside the kernel, it is untrusted.

If adopted, the roadmap's phase 0 shrinks to: the `proofscript` types package, annotation extraction, and a `proofscript check` CLI built on the TS API. The parser fork, loader and content-mapper spike are deferred with the sugar.

## 7. File extensions

With embedded mode, the question mostly dissolves:

- **Implementation code stays `.ts` / `.tsx` / `.mts` / `.cts`** (and `.js` with the same `//@` annotations).
- **Proof modules use `.proof.ts`**, mirroring `.test.ts` / `.spec.ts`. A double extension is only safe because the file is valid TypeScript: every tool that globs `*.ts` handles it. It would be a poor choice for files containing new syntax, which those tools would choke on.

If the dedicated sugar is ever built, the candidates are:

| Extension | Notes |
|---|---|
| **`.pts` / `.ptsx` / `.mpts` / `.cpts`** | Recommended. Parallels `.ts`/`.tsx`/`.mts`/`.cts`. Not registered in GitHub Linguist. Historically used by Pro Tools 5–6 session files and some point-cloud data; low collision risk for source code. |
| `.psts` | Unregistered; less obvious, awkward to say. |
| `.prfts` | Unregistered; unreadable. |
| `.vts` ("verified TS") | Collides with VTK structured-grid files. |
| `.tsp` | Taken by TypeSpec (and TSPLIB). |
| `.ps` | PostScript. |
| `.ts` + a `// @proofscript` pragma | Impossible for new syntax: every tool would parse the file as TS and fail. |
