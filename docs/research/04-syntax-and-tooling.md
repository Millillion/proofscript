# 04 — Concrete Syntax and Tooling Architecture

Research date: 2026-11-02. Scope: how ProofScript, a TypeScript superset with dependent types and formal verification, should be spelled, parsed, checked, integrated with the TypeScript toolchain, and surfaced in editors.

Sources were checked against primary material where possible. I cloned and read `microsoft/typescript-go` (HEAD 2026-08-20), `volarjs/volar.js` (HEAD 2026-10-25) and `nodejs/amaro` (HEAD 2026-10-27). Code citations give repo-relative paths.

---

## 0. Executive summary

1. **The big change in 2026 is TypeScript 7.1's *content mappers*.** TS 7.0 (the Go-native compiler, "Corsa") shipped on 2026-07-08 with no API ([TS 7.0 announcement](https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/)). 7.1 Beta (2026-10-20) adds two things ([TS 7.1 beta](https://devblogs.microsoft.com/typescript/announcing-typescript-7-1-beta/)):
   - a new JS API (`typescript/sync`, `typescript/async`, `typescript/ast`, and so on);
   - **content mappers**: a tsconfig-registered external process that turns a non-TS file extension into virtual TS. It returns span mappings and *its own diagnostics*, the tsc CLI and the TS language server both consume it, and tsc emits `.d.ts` from it.

   The 7.1 post says "Volar's core model is now a first-class citizen." For ProofScript this means `.pts` files can get full TS type checking, IDE features and `.d.ts` emission from stock `tsc`/tsserver, while ProofScript's own checker reports proof errors through the same channel. This is the single most important architectural fact in this report.
2. **Syntax: use a hybrid with a small, keyword-led, fully erasable grammar extension in `.pts` files.** This rests on three design rules:
   - every ProofScript construct either sits in a type or spec position, or is a whole declaration or statement that erases to whitespace;
   - ProofScript never invents a runtime representation; it only attaches ghost information to TypeScript's existing runtime values;
   - existing TS syntax gets dependent meaning wherever possible. For example, `(n: nat) => Vec<T, n>` is already valid TS function-type syntax.

   Pure-TS embeddings and JSDoc annotations are useful as an interop tier and as prior art, but they cannot carry real proofs ergonomically.
3. **Tooling: use a separate front end that delegates to TypeScript; do not fork tsc or tsgo.** The front end is a ProofScript parser that produces (a) a ProofScript AST and (b) virtual TS with span maps. TS checks the runtime fragment, and the ProofScript elaborator and kernel check specs and proofs, using TS's types for runtime expressions through the TS API. Deliver it through:
   - a TS 7.1 content mapper (primary, forward-looking);
   - a Volar.js language plugin on TS 6 (fallback while 7.1 settles);
   - a separate ProofScript LSP channel for the goal view (an "infoview").
4. **Kernel: write it in TypeScript first, small and Lean-like, with proof export to Lean's kernel format for independent re-checking** (lean4export → Lean / nanoda / lean4lean). This is better than "translate to Lean and let Lean be the checker". Consider a Rust/wasm kernel later for speed, and verifying the kernel in ProofScript itself as a long-term dogfooding goal.

---

## Part A — Syntax embedding strategies

The running examples are:

- **(E1)** a theorem `add_comm`;
- **(E2)** an inductive `Vec<T, n>`;
- **(E3)** a function with pre/postconditions and a loop invariant;
- **(E4)** a proof by induction, in tactic and term style.

### A.0 What other verifiers look like (vocabulary to borrow)

| Concept | Lean 4 | Dafny | Verus (Rust) | F* | Idris 2 | Liquid Haskell |
|---|---|---|---|---|---|---|
| Theorem | `theorem add_comm (a b : Nat) : a + b = b + a := by …` | `lemma AddComm(a: nat, b: nat) ensures a + b == b + a {}` | `proof fn lemma_add_comm(a: nat, b: nat) ensures a + b == b + a {}` | `let add_comm (a b:nat) : Lemma (a + b == b + a) = ()` | `addComm : (a, b : Nat) -> a + b = b + a` | `{-@ addComm :: a:Nat -> b:Nat -> {a + b == b + a} @-}` |
| Inductive | `inductive Vec (α : Type) : Nat → Type where \| nil : Vec α 0 \| cons : α → Vec α n → Vec α (n+1)` | `datatype List<T> = Nil \| Cons(head: T, tail: List<T>)` | Rust `enum` + `spec fn` views | `type vec (a:Type) : nat -> Type = \| Nil : vec a 0 \| Cons : …` | `data Vect : Nat -> Type -> Type where …` | Haskell `data` + measures |
| Pre/post | (types / subtypes) | `requires P ensures Q` | `requires P, ensures Q,` | `Pure t (requires P) (ensures Q)` | (types) | refinement types `{v:Int \| v >= 0}` |
| Loop invariant | (n/a, functional) | `while c invariant I decreases d {}` | `while c invariant I, decreases d, {}` | (n/a) | (n/a) | (n/a) |
| Termination | `termination_by`, `decreasing_by` | `decreases e` | `decreases e` | `(decreases e)` | totality checker | `/ [e]` metrics |
| Proof style | tactics `by`, terms, `calc` | auto (SMT) + `calc`, `assert … by {}` | auto (SMT) + `assert … by {}` | SMT + tactics (Meta-F*) | terms, holes `?h` | SMT, proof combinators `===`, `***` QED |
| Ghost code | `Prop`, erased automatically | `ghost var`, `lemma` | `spec`, `proof`, `tracked`, `ghost` | `GTot`, erased | quantities `0` | measures |

Takeaways for ProofScript:

- **The Dafny/Verus clause vocabulary** (`requires`, `ensures`, `invariant`, `decreases`) is the most widely recognised spec vocabulary among mainstream programmers. JML, ACSL, Spec#, Whiley and Verus all use it. Adopt it verbatim.
- **Lean's `theorem` … `by` tactic block** is the de-facto vocabulary for interactive proofs, and Lean's Mathlib is the gravity well. Adopt `theorem`/`lemma`, `by`, `calc`, `induction`, `cases`, `simp`, `omega`, `rfl`, `exact`.
- **Verus's `spec`/`proof`/exec mode split** is the closest analogue to what ProofScript needs: ghost code that erases versus runtime code that stays. Verus also shows that clauses can be added to an existing language's function syntax (it uses a proc-macro wrapper, `verus! { … }`), which parallels our "extended grammar in a different file type".

### A.1 Strategy 1 — New syntax extending the TS grammar (`.pts` files)

#### Example snippets

```ts
// E1: a theorem. Erases entirely.
theorem add_comm(a: nat, b: nat): a + b === b + a by {
  induction a;
  simp;
}

// E2: an inductive family. Two flavours.

// (a) "ghost-indexed view" of an existing runtime type (recommended default):
//     the runtime value is an ordinary readonly T[]; n is erased.
type Vec<T, n: nat> = (xs: readonly T[]) where xs.length === n;

// (b) a genuinely inductive *ghost* type (no runtime representation at all):
inductive Fin(n: nat) {
  zero(k: nat): Fin(k + 1);
  succ(k: nat, i: Fin(k)): Fin(k + 1);
}

// E3: function with contracts and a loop invariant
function sumTo(n: nat): nat
  requires n <= 1_000_000
  ensures r => r === n * (n + 1) / 2
{
  let s = 0;
  let i = 0;
  while (i < n) {
    invariant i <= n && s === i * (i + 1) / 2;
    decreases n - i;
    i++;
    s += i;
  }
  return s;
}

// E4: tactic proof and term proof of the same lemma
theorem append_length<T>(xs: List<T>, ys: List<T>):
  length(append(xs, ys)) === length(xs) + length(ys)
by {
  induction xs with
  | nil => simp [append, length]
  | cons(h, t, ih) => simp [append, length, ih]; omega
}

theorem append_length2<T>(xs: List<T>, ys: List<T>):
  length(append(xs, ys)) === length(xs) + length(ys)
{
  switch (xs.tag) {
    case "nil":  return rfl;
    case "cons": return congrArg(n => n + 1, append_length2(xs.tail, ys));
  }
}
```

After erasure (whitespace-preserving, so line and column positions are unchanged), `sumTo` becomes exactly the TS a developer would have written:

```ts
function sumTo(n: number): number


{
  let s = 0;
  let i = 0;
  while (i < n) {


    i++;
    s += i;
  }
  return s;
}
```

`nat` erases to `number` (or `bigint`; the numeric semantics question belongs to the type-theory report). The `theorem`, `inductive` and `type … where` declarations erase completely, or to a plain `type Vec<T, n> = readonly T[]` when the alias is exported for TS consumers.

#### How TypeScript itself adds contextual keywords safely

TS has added many words without reserving them. It disambiguates them with *same-line lookahead* and *position*. From the typescript-go parser (`internal/parser/parser.go`):

- **`as` / `satisfies`** are binary operators only when there is **no preceding line break**: `if p.hasPrecedingLineBreak() { break }`, with the comment "Make sure we *do* perform ASI for constructs like `var x = foo \n as (Bar)`".
- **`using`** starts a declaration only if the next token is a binding identifier or `{` **on the same line** (`isUsingDeclaration` → `nextTokenIsBindingIdentifierOrStartOfDestructuringOnSameLine`). `using[x]` is deliberately not treated as a declaration, because it collides with element access.
- **`type`, `interface`, `defer`** are declarations only if followed by an identifier on the same line (`nextTokenIsIdentifierOnSameLine`). **`abstract`, `accessor`, `declare`, `readonly`** and similar modifiers are modifiers only if no line break follows ("ASI takes effect for this modifier").
- **`asserts x is T`** and **`infer`** live only in type positions. Type positions are a separate grammar that runtime JS never enters, so there is no ambiguity.

The general recipe is: a contextual keyword followed on the same line by a token that would otherwise be a syntax error (usually an identifier), or a keyword confined to type-only grammar.

#### Ambiguity analysis for ProofScript additions

| Addition | Where | Ambiguity risk | Resolution |
|---|---|---|---|
| `theorem f(…)`, `lemma f(…)`, `inductive F…`, `axiom f…` | statement start | `theorem\nf(x)` is legal JS (ASI gives two statements) | Same-line rule, as for `type`/`interface`: keyword + identifier on one line. In `.pts` also *reserve* these words (see below). |
| `requires e` / `ensures e` / `decreases e` after a function signature | between `)` or return type and `{` | None. Any token there is currently a syntax error in TS. | Clause list terminated by `{`. Not allowed on arrow functions: `(x): T requires …` collides with conditional-expression arrow ambiguities, which TS already resolves by speculative parsing. An arrow function that needs contracts is written as a `function` declaration or expression instead. |
| `invariant e` / `decreases e` inside a loop body | statement position | `invariant (x)` is a legal call expression; `invariant\n{…}` is a legal expression statement | Dafny-style placement `while (c) invariant I { … }` is **ambiguous** in JS: `while (c) invariant` parses as a loop whose body is the identifier `invariant`. So put clauses as the first statements *inside* the body, and **reserve** `invariant`, `decreases`, `assert`, `assume`, `ghost` in `.pts`. |
| `by { … }` / `by tactic` after a theorem type | after `:` type | None (position is new) | — |
| Value parameters in generics `type Vec<T, n: nat>` | type-parameter list | None. `<n: nat>` is not TS syntax. | — |
| Value arguments in type args `Vec<T, n + 1>` | type positions | `n + 1` is not a TS type, so no ambiguity; bare `n` could be a type or a value | Parse a unified "type-or-term" grammar inside type arguments and resolve by **name binding** in the elaborator, as Lean does (types and terms share one syntax). |
| Pi types `(n: nat) => Vec<T, n>` | type positions | None: already valid TS function-type syntax | Give it dependent meaning: the parameter name scopes over the result. Virtual TS keeps it with the index erased. |
| Refinement types | type positions | Liquid-style `{ v: number \| v >= 0 }` **is ambiguous**: it parses as an object type whose member type is a union. Lean's `{ x : T // p }` uses `//`, which is a JS comment. | Use `(x: number) where x >= 0`. After `)` the TS parser already looks ahead for `=>` to decide on a function type, and `where` there is currently an error, so it is unambiguous. |
| Propositions as types `a + b === b + a` | return-type position of `theorem` | In TS, a type cannot be an expression | Only inside `theorem`/`ensures`/`where`/`invariant`, where the grammar is the *spec-expression* grammar (TS expressions plus `forall`, `exists`, `==>`, `old(…)`). |
| `==>` implication | spec expressions | `a ==> b` lexes as `a == > b` → error in JS | Lex `==>` as one token only in spec context. |
| JSX | `.ptsx` | Generic arrow `<T>(x) =>` vs JSX tag, the usual TSX problem | Inherit the TSX rules verbatim in `.ptsx`. Add no new `<`-led syntax. |

**Reserved words.** Because `.pts` is a new file type, ProofScript can *reserve* its keywords there, as strict mode reserved `let`, `static` and `yield`. A file that binds an identifier named `invariant` gets a diagnostic and a quick fix to rename or alias it, e.g. `import { invariant as tinyInvariant } from "tiny-invariant"`. This removes almost all ambiguity at the cost of a one-time rename on opt-in.

#### Pros and cons

- **Pros:**
  - The most readable option, and the closest to Dafny, Verus and Lean.
  - The parser knows exactly what is spec and what is code.
  - Errors point at real syntax.
  - Erasure is trivial and position-preserving.
  - Leaves room to grow (`calc`, `match`, tactic blocks) without contortions.
- **Cons:**
  - Every existing tool (Node, esbuild, Vite, Prettier, ESLint, Biome) rejects the syntax unless a strip step runs first or a plugin exists.
  - Needs a custom file extension, which content mappers now make cheap for tsc and tsserver, plus our own parser.
  - Tracking new TS syntax is our job.

### A.2 Strategy 2 — Pure-TS embedding (zero new syntax)

Everything below parses and type-checks with stock tsc.

```ts
import type { Nat, Proof, Eq, Add, Theorem } from "proofscript";
import { requires, ensures, invariant, decreases, theorem, by } from "proofscript";

// E1, as a type-level computation over Peano/tuple naturals (bounded!)
type add_comm<A extends Nat, B extends Nat> = Eq<Add<A, B>, Add<B, A>>; // checked by instantiation only

// E1, as a "proof object" whose meaning ProofScript gives to a TS function
export const add_comm = theorem((a: number, b: number) => a + b === b + a, by`
  induction a; simp
`);

// E2: branded/phantom index
type Vec<T, N extends number> = readonly T[] & { readonly length: N };
// works for literal N, collapses to `number` for anything computed

// E3: esverify-style pseudo-calls (https://github.com/levjj/esverify)
function sumTo(n: number): number {
  requires(n >= 0 && Number.isInteger(n));
  ensures((r: number) => r === n * (n + 1) / 2);
  let s = 0, i = 0;
  while (i < n) {
    invariant(i <= n && s === i * (i + 1) / 2);
    decreases(n - i);
    i++; s += i;
  }
  return s;
}

// E4 (term style): the proof as a recursive function returning Proof<…>
function append_length<T>(xs: List<T>, ys: List<T>):
  Proof<"length(append(xs, ys)) === length(xs) + length(ys)"> {
  return xs.tag === "nil" ? refl() : cong(append_length(xs.tail, ys));
}
```

What is achievable:

- **Exact type-level equality** with the well-known trick `(<X>() => X extends A ? 1 : 2) extends (<X>() => X extends B ? 1 : 2)`.
- **Bounded computation** over literal numbers or tuples. hkt-toolbelt and many "type-level TS" demos show that TS's conditional and recursive types are Turing-complete in principle.
- **Discriminated-union exhaustiveness** (ts-pattern; `never` checks).
- **Branded refinements**, as in Effect Schema's `Brand` and `filter` combinators, which pair a runtime check with a nominal brand.
- **Pseudo-call contracts**, which esverify actually verified with Z3 ([esverify](https://github.com/levjj/esverify)).

What is awkward or impossible:

- **No value dependency.** A type cannot mention a runtime variable `n`; only `typeof n`, which widens to `number`. Pi types collapse.
- **Proof by type evaluation is bounded.** Proofs run into "Type instantiation is excessively deep and possibly infinite", the roughly 50-level / tail-recursive ~1000 depth limits. No real induction over unbounded naturals is possible.
- **Unsound substrate.** `any`, bivariance and casts make TS "proofs" meaningless as certificates.
- **Specs as strings or template literals** (`Proof<"…">`, `` by`…` ``) lose TS name resolution, rename and highlighting unless a language plugin re-parses them, which is half of Strategy 1 anyway.
- **Pseudo-calls are runtime code.** `requires(…)` survives into JS unless a bundler strips it, and the closures in `ensures(r => …)` allocate. Decorators cannot attach to functions or loops, and Node type stripping rejects TS experimental decorators.

**Verdict:** pure-TS embedding works well for an interop and "lite" tier: branded `Nat`, `Proof<P>` as an opaque type in generated `.d.ts`, and runtime contract shims. It is a poor home for proofs. It is valuable as the **output** format for `.d.ts` consumers, not as the input language.

### A.3 Strategy 3 — JSDoc / comment annotations

Precedents:

- **JML:** `//@ requires x > 0;`
- **Frama-C ACSL:** `/*@ requires \valid(p); ensures \result >= 0; loop invariant …; */`
- **Liquid Haskell:** `{-@ … @-}`
- **Refined TypeScript:** `/*@ … */` refinement signatures such as `type nat = {v:number | 0 <= v}` ([Vekris, Cosman, Jhala, PLDI 2016](https://goto.ucsd.edu/~pvekris/docs/pldi16.pdf); [arXiv 1604.02480](https://ar5iv.labs.arxiv.org/html/1604.02480))
- **TypeScript's own `checkJs`/JSDoc type annotations.**

```ts
/*@ theorem add_comm(a: nat, b: nat): a + b === b + a by { induction a; simp } @*/

/**
 * @requires n >= 0
 * @ensures r => r === n * (n + 1) / 2
 */
function sumTo(n: number): number {
  let s = 0, i = 0;
  while (i < n) {
    //@ invariant i <= n && s === i * (i + 1) / 2
    //@ decreases n - i
    i++; s += i;
  }
  return s;
}
```

- **Pros:**
  - Zero tooling breakage: plain `.ts`, runs under `node`, every bundler, Prettier and ESLint as-is.
  - The best possible story for "annotate an existing codebase without renaming files".
  - LH and ACSL prove that serious verification can live in comments.
- **Cons:**
  - Comments are second-class citizens. Formatters reflow them and minifiers drop them, and comment-to-node attachment is heuristic (TS's own JSDoc attachment has many edge cases).
  - No highlighting or IDE support without an extension.
  - Multi-line tactic proofs inside comments are miserable to write.
  - Two languages in one file without a clear parse boundary.
  - Most fatal for a "Lean, but TypeScript" pitch: it signals that proofs are not part of the language.

**Verdict:** worth supporting later as an optional "spec-only lite mode" for `.ts` files (contracts and invariants, discharged automatically). Not for theorems and tactic proofs.

### A.4 Strategy 4 — Hybrid (recommended)

Use a **small, closed set of new erasable syntax** in `.pts`, and put everything else in **library-level constructs written in ProofScript itself**: tactics, `Nat`/`Int` theories, `List`, `Vec`, `Eq`, `Decidable`, simp sets. The analogy is Lean: the core syntax is small and most surface notation comes from libraries and macros.

The new syntax is roughly:

1. **Declarations:** `theorem`, `lemma`, `axiom`, `inductive`, `structure` (ghost), `spec function`, `ghost let`.
2. **Clauses:** `requires`, `ensures`, `decreases`, `modifies` (later), and `invariant`/`decreases` statements in loops.
3. **Proof blocks:** `by <tactic-block>`, `calc { … }`, `assert e by { … }`.
4. **Type positions:** value parameters `<n: nat>`, value arguments `Vec<T, n + 1>`, dependent function types, `(x: T) where P`.
5. **Spec-expression extensions:** `forall`, `exists`, `==>`, `<==>`, `old(e)`, `result`.

Library-level pieces include `Proof<P>`, `Eq<A, B>`, tactic definitions and `@simp`-style attributes, which could later be spelled as decorators on `theorem` declarations.

#### Fitting the TC39 Type Annotations proposal and Node type stripping

- **The TC39 proposal** ([proposal-type-annotations](https://github.com/tc39/proposal-type-annotations)) is still **Stage 1**, with no substantive update since the 2023 plenaries.
  - Its erasable regions are annotations after `:`, `interface`/`type` declarations, generics on declarations, `import type`/`export type`, `as`, `!`, `?` and `this` parameters.
  - Its bounding rule for type syntax is explicitly unsettled ("anything within matching parentheses and brackets" is floated as a first step).
  - It excludes enums, namespaces and parameter properties.
  - **Most ProofScript additions do not fit**: `requires` clauses, `theorem` declarations and `invariant` statements are new statement and clause forms, not annotations.
  - What *could* fit is anything inside an existing type region: dependent function types, `<T, n: nat>` (if bracket-balanced token soup is allowed), `where` refinements inside a `type` alias body, and `Proof<…>` types.
  - Even in the most optimistic case, ProofScript can't rely on this proposal. It can only aim to be *robust* to it by keeping new syntax bracket-balanced and keyword-led.
- **Node type stripping** ([Node docs](https://nodejs.org/api/typescript.html)) is now **stable** (v25.2 / v24.12) and on by default.
  - It runs Amaro, a wasm build of SWC's TS parser in `strip-only` mode that replaces types with whitespace ([amaro](https://github.com/nodejs/amaro)).
  - It only handles `.ts`/`.mts`/`.cts` (not `.tsx`), never under `node_modules`, ignores `tsconfig`, and errors on non-erasable syntax (enums, runtime namespaces, parameter properties, import aliases, decorators).
  - `--experimental-transform-types` was removed in Node 26.
  - SWC's parser rejects anything that is not TS, so **no new keyword survives `node --strip-types`, even if it sits in a type position**: `<n: nat>` and `where` are parse errors to SWC.
  - Only Strategy 2 and 3 code runs under bare `node`. Strategy 1 and 4 code needs either a build step or a registered loader. Amaro itself documents `module.registerHooks()`-based loaders (`node --import=amaro/strip`), and ProofScript would ship an equivalent `node --import=proofscript/register`.
  - **Design consequence:** make ProofScript's erasure *whitespace-preserving*, exactly like Amaro. Then `.pts → .ts` and `.pts → .js` keep every line and column, no source maps are needed for stack traces, and the output of `pts strip foo.pts` piped through Amaro is byte-for-byte what tsc or type stripping would produce from the hand-erased TS.

#### How JS developers will read proofs

- **`by { induction n; simp }`.** Braces plus semicolons read as "a block of commands". It is closer to JS than Lean's layout-sensitive `by\n  induction n <;> simp`. Recommend brace-delimited tactic blocks with `;` or newline separators, and `case nil => …` / `| cons(h, t, ih) => …` arms. Keep Lean's tactic *names* so Lean users and LLMs trained on Mathlib transfer directly.
- **Term proofs as recursive functions** (`switch` plus `return rfl`) are the most approachable form for TS developers, because "a proof is a function" maps onto Curry-Howard without jargon. Dafny's experience is that most users write lemmas as recursive functions with `assert`s and let the solver fill gaps. ProofScript should make that the default and keep `by` blocks for when automation fails.
- **`calc` blocks** are a familiar chain-of-equalities notation and read well in JS braces:

  ```ts
  calc {
    sum(xs ++ ys);
    === sum(xs) + sum(ys)  by { simp [sum_append] };
    === sum(ys) + sum(xs)  by { omega };
  }
  ```

---

## Part B — Tooling architecture

### B.1 Fork, wrap, or delegate to the TypeScript compiler?

**State of TypeScript, November 2026:**

- **TS 6.0** (2026-03-23) is the last JS-codebase ("Strada") release.
- **TS 7.0** (2026-07-08) is the Go port, about 10x faster. It ships as the `typescript` package with `tsc`, but **"does not ship with an API"**. The post recommends using 7.0 only "in scenarios where language server plugins are not required". Vue, MDX, Astro, Svelte and Volar stay on 6.0 through `@typescript/typescript6` (`tsc6` + 6.0 API) ([7.0 post](https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/)).
- **TS 7.1 Beta** (2026-10-20) adds:
  - `typescript/sync` and `typescript/async` clients (compiler options, program, type-checker), `typescript/fs`, `typescript/ast`, `typescript/ast/is` and `typescript/ast/factory`. API objects bridge the Go and JS runtimes and must be disposed.
  - **Content mappers** ([7.1 beta post](https://devblogs.microsoft.com/typescript/announcing-typescript-7-1-beta/)).

**Content mappers in detail** (read from `typescript-go/internal/contentmapper/*.go` and `internal/spanmap/spanmap.go`):

- **Configuration.** In tsconfig:

  ```json
  "contentMappers": [{ "package": "...", "extensions": [".pts"], "options": {…} }]
  ```

  The package declares `"typescript": { "contentMapper": { "exec": [...] } }` in its `package.json`. Built-in extensions (`.ts`, `.tsx`, `.js`, `.json`, …) **cannot be registered**; that is diagnostic 100021, checked by exact match, so a compound extension such as `.proof.ts` is not rejected. Using mappers requires `tsc --runExternalCode`. In VS Code it also requires workspace trust and a mapper permission.
- **Process model.** tsc spawns the mapper as a child process and speaks JSON-RPC over `internal/ipc`. One process serves all projects using the same mapper name and version.
- **Protocol** (`ProtocolVersion = 1`): `initialize` (choose UTF-8 or UTF-16 positions, diagnostic source prefix), `openProject` (receives the tsconfig path, mapper options and effective compiler options; can return a config fingerprint and watched files), `transform` (`{fileName, content, projectHandle}`) and `closeProject`.
- **`transform` result:**
  - the virtual `text`;
  - an `extension` (`.ts`/`.tsx`/`.js`/…);
  - a **SpanMap**;
  - **mapper-authored `diagnostics` in original-source coordinates**: this is how ProofScript proof failures can appear in `tsc` output and in the editor's Problems pane;
  - optional **`supplemental` outputs**: extra unnamed virtual TS files, e.g. ambient declarations;
  - `diagnosticDirectives`: framework-style ignore/expect directives over virtual ranges.
- **SpanMap.** Unlike a source map, it records explicit *segments*. `KindVerbatim` segments are length-preserving and map 1:1. `KindAtom` maps a span as a whole, for renamed or short expressions. `KindAlias` is an atom asserting both sides name the same entity, so diagnostics can substitute the original name. Each segment has a 20-bit `Feature` mask (hover, completion, definition, references, rename, inlay hints, semantic tokens, code actions, …). Diagnostics cannot be masked off. Unmapped virtual text is "synthesized".
- **Emit.** For content-mapped files, tsc emits **`.d.ts`** (without declaration maps for now), but **JS emit is "owned by the external content mapper or build tool"** (`internal/compiler/emitter.go`).

**Options compared:**

| Option | Assessment |
|---|---|
| Fork tsgo (Go) and add dependent types to its checker | **No.** The TS checker is about 50k lines tuned for structural, unsound, inference-heavy typing. Dependent types and a proof kernel don't belong inside it. The upstream port moves fast (7.x API work, content mappers), so a fork would be a permanent rebase tax. We would also own all of TS's IDE features. |
| Fork the TS 6 JS compiler | Tempting because it is now **frozen**, but that freezes ProofScript at TS 6 syntax and semantics while the ecosystem moves to 7. Reasonable only for *borrowing the parser* (see B.4). |
| tsserver plugin only | Cannot add syntax (B.3). |
| **Separate front end that delegates to TS (recommended)** | ProofScript parses `.pts` and produces virtual TS for TS to check, using TS 7.1 content mappers or Volar on TS 6. Its own elaborator queries TS's types for runtime expressions through the TS API, and it checks specs and proofs itself. The same split as Vue/Svelte/Astro and as Verus (which reuses rustc's front end, then runs its own VC generation). |

**The two-checker split, concretely:**

1. The ProofScript parser produces the PS-AST and, from it, `virtual.ts` with a SpanMap.
2. **TS checks `virtual.ts`.** This covers runtime code typing, imports, and TS IDE features inside `.pts`.
3. **ProofScript's elaborator** walks the PS-AST. For each runtime expression it needs typed, such as the `xs` in `length(xs)`, it asks the TS program (via `typescript/sync`, or the TS 6 API in Volar mode) for the type at the mapped virtual position. It then translates TS types into ProofScript core types (`number` → `Float64`/`Real` view, `bigint` → `Int`, unions → sums, and so on), elaborates specs and proofs into core terms, and calls the kernel.
4. Kernel errors become content-mapper `diagnostics` or LSP diagnostics in `.pts` coordinates.

One subtlety is that the content-mapper protocol hands the mapper a single file's text and gives it no access to the TS checker. The mapper must therefore run its own project-level analysis. It gets the tsconfig path and compiler options in `openProject`, so it can create its own `typescript/sync` program, or more simply maintain a ProofScript-only project graph and use the TS API lazily. The supplemental-output mechanism lets the mapper inject ambient declarations, for example `declare const __ps_ghost: unique symbol`.

**Virtual TS trick for specs:** emit specs as *real TS expressions inside never-called closures*. For example:

```ts
ensures r => r === n * (n + 1) / 2   →   ;(__ps.ensures)((r: number) => r === n * (n + 1) / 2);
```

The closure is placed in a synthesized region, with the expression text mapped verbatim. This gives hover, go-to-definition, find-references and **rename across code and specs** for free, which is exactly how Vue templates get TS features in Volar. Only spec-only constructs (`forall`, `==>`, tactic blocks) are left unmapped or masked to `FeatureNone`.

### B.2 Volar.js "virtual code" architecture

Volar ([volarjs.dev](https://volarjs.dev/reference/languages/)) is the shared language-tooling framework behind Vue (`vue-tsc`, Vue Language Tools), Astro, MDX, Ripple and others. The mechanics, from `volar.js/packages/language-core/lib/types.ts` and `packages/source-map`:

- **`LanguagePlugin`** has these members:
  - `extensions` (e.g. `['.pts']`);
  - `getLanguageId(scriptId)`;
  - `createVirtualCode(scriptId, languageId, snapshot, ctx)` → `VirtualCode`;
  - optional `updateVirtualCode` for incremental reparsing, and `disposeVirtualCode`;
  - a `typescript` sub-object (in TS-plugin mode) naming which embedded code is the "service script" and its `ScriptKind`, plus whether the source file itself should be hidden from TS.
- **`VirtualCode`** is `{ id, languageId, snapshot, mappings: CodeMapping[], embeddedCodes?: VirtualCode[], associatedScriptMappings?, linkedCodeMappings? }`. Embedded codes form a tree, so one `.pts` file could expose a `ts` virtual code for TS and a `ps-spec` code for a custom service.
- **`Mapping<CodeInformation>`** is `{ sourceOffsets[], generatedOffsets[], lengths[], generatedLengths?, data }`. `CodeInformation` flags gate features per mapping:
  - `verification` (diagnostics and code actions; a `shouldReport(source, code)` filter can suppress specific TS errors arising in generated code);
  - `completion`;
  - `semantic` (hover, inlay hints, semantic tokens);
  - `navigation` (definition, references, rename; with `resolveRenameNewName`/`resolveRenameEditText` hooks);
  - `structure`;
  - `format`.
- **Hosting modes:**
  1. A **standalone LSP** (`@volar/language-server`) that runs its own TS language service over the virtual files.
  2. A **tsserver plugin** (`@volar/typescript`, `createLanguageServicePlugin`), which decorates TS's `LanguageServiceHost` so tsserver sees virtual code for `.pts` and proxies results back through the mappings. This is how Vue makes `.ts` files importing `.vue` work in the normal TS server.
  3. A **CLI wrapper** (`runTsc`), which patches `tsc` to accept extra extensions. This is how `vue-tsc` works.
- **Mapping to TS 7.1.** Volar's `Mapping` + `CodeInformation` maps almost one-to-one onto tsgo's `spanmap.Segment` + `Feature`; 7.1 explicitly calls Volar's model "first-class". **Design the ProofScript virtual-code generator to output a neutral `{segments, features}` structure, with thin adapters to Volar `CodeMapping[]` and tsgo SpanMap JSON.**
- **Limitations:**
  - **Volar is tied to the TS 6 API** until it migrates to 7.1's API and content mappers.
  - Volar cannot change TS's *semantics*. Only what is expressible in virtual TS gets checked, which is fine because proofs go to our checker.
  - Generated code must itself be valid TS. Errors inside synthesized code are confusing, so mask them with `verification: false` or `shouldReport`.
  - Rename and edit across non-verbatim mappings is lossy; text edits need verbatim geometry, the same rule as tsgo's spanmap.
  - TS-plugin mode relies on host patching that can break across TS versions.
  - Memory and CPU roughly double, because there are two services over the same code.

### B.3 tsserver plugins, LSP, and an infoview for interactive proving

- **TS language-service plugins** (`compilerOptions.plugins`) can decorate language-service methods (completions, diagnostics, quick info) but **cannot change parsing, the set of recognised file extensions, or tsc CLI behaviour**. That is why Volar's TS-plugin mode has to patch the host, and why Civet's FAQ says VS Code's TS server "can't resolve non .ts/.js, not even with plugins", leading Civet to its own LSP ([Civet](https://github.com/DanielXMoore/Civet)). TS 7.0 does not support LS plugins; 7.1's replacement plugin point *is* content mappers.
- **The proof-state UI must be a separate channel.** Lean's infoview is the model:
  - The Lean server implements LSP plus custom requests (`$/lean/plainGoal`, `$/lean/plainTermGoal`, `$/lean/fileProgress`) and a **session-based RPC layer** (`$/lean/rpc/connect`, `$/lean/rpc/call`, `$/lean/rpc/release`, `$/lean/rpc/keepAlive`). Server-side functions are registered with `@[server_rpc_method]`, e.g. `Lean.Widget.getInteractiveGoals`, and can return references to server objects.
  - The **infoview** (`@leanprover/infoview`, from the `vscode-lean4` repo) is a React app in a VS Code webview. On each cursor move it shows goals, hypotheses, expected type and messages, with hover and "go to definition" inside rendered expressions (interactive `CodeWithInfos`).
  - **User widgets:** a Lean declaration tagged `@[widget_module]` carries an ES module exporting a React component; widget instances pair a module hash with props, which may contain RPC references ([Lean.Widget.UserWidget](https://lean-lang.org/doc/api/Lean/Widget/UserWidget.html), [Lean.Widget.Types](https://lean-lang.org/doc/api/Lean/Widget/Types.html)). ProofWidgets4 builds on this.
  - For ProofScript, whose users are web developers, widgets are a natural fit: proof visualisations can simply be TSX components.
- **ProofScript editor UX:**
  1. A `proofscript` VS Code extension (and a generic LSP for Zed and Neovim) with a goal panel, a webview like Lean's.
  2. Requests: `$/proofscript/goals {uri, position}` → `{goals: [{hyps, target}], messages}`, plus an RPC layer for interactive terms.
  3. Incremental elaboration with per-declaration snapshots, so tactic edits re-check only the current theorem, as Lean's `Language.Lean` snapshot trees do.
  4. Inlay hints for inferred invariants and decreases measures. Code lenses on `theorem`s show ✓, ✗ or time.
  5. `sorry`/`admit` with a warning, and a holes UX (`?goal`) borrowed from Idris and Agda.
  6. Because proof errors also flow through content-mapper diagnostics, `tsc` in CI fails on broken proofs with no extra tool. That is a strong adoption story: `tsc --runExternalCode` is the only CI change.

### B.4 Parser options for the extended grammar

| Option | Notes |
|---|---|
| **Hand-written fork of the TS parser** | TS's scanner and recursive-descent parser (TS 6 `parser.ts`/`scanner.ts`, or tsgo's `internal/parser`) are the reference for every TS ambiguity: ASI, arrow-function speculation, generics vs `<`, JSX. Porting or forking gives exact TS compatibility, and TS 6 being frozen makes a JS fork stable. The cost is tracking new TS syntax added in 7.x by porting from Go. |
| **Own parser in TS with full TS grammar** (Civet's approach) | Civet uses its own PEG parser generator (Hera) for a full TS superset that compiles to TS or JS. It is flexible, but re-implementing TS's grammar quirks has a long tail. |
| **Babel plugin** | Babel *parser* plugins are internal; adding syntax means forking `@babel/parser`, which Flow and others did historically. Not recommended. |
| **SWC / oxc** | Fast Rust parsers with complete TS support. Neither supports syntax plugins; a fork is needed. A good choice *if* the front end is in Rust. oxc also has `isolatedDeclarations` emit and a fast transformer. |
| **tree-sitter** | For editor highlighting, folding, GitHub and Zed, not for the compiler. `tree-sitter-typescript` is built as `grammar(require('tree-sitter-javascript/grammar'), …)` via `common/define-grammar.js`, so ProofScript can extend it the same way (`tree-sitter-proofscript` adds the clause, theorem and tactic rules). Ship a TextMate grammar for VS Code too. |
| How others add syntax | **Vue:** SFC block splitter plus `@babel/parser` for expressions, then Volar codegen. **Svelte:** own template parser with Acorn (plus TS plugin) for script islands. **Astro:** a Go/wasm compiler with a TSX output for the language server. **Marko:** `htmljs-parser` plus Babel. **Flow:** its own OCaml parser, with Babel and Hermes parsers. **Ripple:** a `.ripple` TS superset with `component` and `track`, and a Volar-based VS Code extension ([ripplejs.com](https://www.ripplejs.com)). **Civet:** full PEG grammar compiling to TS, with its own LSP wrapping the TS LS. |

**Recommendation:** write a hand-written recursive-descent parser in TypeScript, **derived from TS 6's `scanner.ts`/`parser.ts`**. It is MIT/Apache-licensed and keeps exact TS behaviour. It extends the scanner with the reserved words and `==>`, and the parser with clause, theorem, tactic and spec-expression productions.

A cheaper *MVP* alternative is a **"blanking pre-pass" that never parses TS itself**. It uses a TS-aware tokenizer (templates, regex, comments, JSX) to find ProofScript constructs, which are all keyword-led and brace-balanced. It blanks them to produce TS, parses them separately, and lets the real TS parser handle the rest. This is how a first version can ship in weeks; the full fork follows.

### B.5 Build integration

- **Type checking in CI:** `tsc --runExternalCode` with `contentMappers: [{ package: "proofscript", extensions: [".pts", ".ptsx"] }]` on TS ≥ 7.1. On TS 6, use a `pts-tsc` wrapper on Volar's `runTsc`, as `vue-tsc` does. Both paths report TS errors *and* proof errors.
- **JS emit:** owned by ProofScript, because tsc does not emit JS for content-mapped files. `pts build` does a whitespace-preserving erase of ProofScript constructs and then a type strip via Amaro or oxc, producing the same JS as tsc would for the erased TS when the project uses `erasableSyntaxOnly`/`verbatimModuleSyntax`. **Require `erasableSyntaxOnly` in ProofScript projects** so "same JS as type stripping" holds exactly.
- **`.d.ts`:** tsc emits `.d.ts` for content-mapped files from the virtual TS. Design the virtual TS so exported signatures erase refinements to base types, e.g. `function sumTo(n: number): number`, keeping plain-TS consumers unaffected. For ProofScript consumers, embed full specs in the `.d.ts` as structured doc comments (`/** @pts requires n <= 1000000 … */`) or ship a sidecar `foo.d.pts` (the analogue of Lean's `.olean` interface). The **sidecar is cleaner and versionable**; the comment form survives every packaging tool. Pick the sidecar and fall back to comments if packaging pain appears.
- **`isolatedDeclarations`:** ProofScript should *require* explicit types on exported functions (contracts need them anyway). Then the mapper can produce `.d.ts`/`.d.pts` per file without whole-program checking, and fast tools such as oxc can emit declarations in parallel.
- **Trust boundary:** plain-TS callers of a ProofScript function aren't verified to meet `requires`. Offer `pts build --boundary-checks` to emit runtime contract checks only on exported entry points, following Racket's contract boundaries. This is the one place where emitted JS intentionally differs, and it is opt-in.
- **Module resolution:**
  - In `.pts` and `.ts` files, `import { sumTo } from "./sum.pts"` resolves under content mappers, since registered extensions join program inclusion and resolution.
  - For emitted JS, `pts build` rewrites `.pts` → `.js` specifiers, as TS 5.7's `rewriteRelativeImportExtensions` does for `.ts`.
  - `allowImportingTsExtensions` semantics apply.
- **Runtimes and bundlers:** Node type stripping does not handle `.pts`, so ship `node --import proofscript/register`, a `module.registerHooks` loader that erases and then strips, mirroring `amaro/strip`. Ship small plugins for Vite/Rollup (`transform` hook), esbuild (`onLoad` for `/\.pts$/`), Bun (`Bun.plugin`), Vitest and Jest. Each is about 20 lines because erasure is a pure text transform.
- **Project references** work unchanged, since `.pts` files are just more inputs to a tsconfig.
- **Extension choice:**
  - **`.pts`** (with `.ptsx` for JSX). Content mappers forbid built-in extensions, and the honest signal "this is not plain TS" prevents other tools from mis-parsing.
  - **`.proof.ts`** passes the content-mapper validation, but it would be *wrongly* processed as plain TS by Node, esbuild, Vite and ESLint, all of which key on the final `.ts`. Reject it.
  - **A `// @proofscript` pragma in `.ts`** has the same problem, and content mappers cannot claim `.ts` at all. A pragma only makes sense for the comment-based "lite" mode (A.3), where the file *is* valid TS.

### B.6 Implementation language for checker and kernel

| Option | Pros | Cons |
|---|---|---|
| **TypeScript** | Same ecosystem as users and the content-mapper process (a Node child process anyway). Runs in the browser (playground, docs, LLM tooling). Direct use of `typescript/sync` and Volar. Contributors are TS developers. Dogfooding: the kernel can later be *written in ProofScript and verified in ProofScript*, a TS analogue of lean4lean (Lean's kernel checked in Lean; [Carneiro, TYPES 2025](https://drops.dagstuhl.de/storage/00lipics/lipics-vol384-types2025/LIPIcs.TYPES.2025.2/LIPIcs.TYPES.2025.2.pdf)). | Slower for heavy normalisation (big `decide`/`simp` proofs); GC pressure on large terms. Mitigations: hash-consing, de Bruijn levels with closures (NbE), and later a wasm kernel. |
| **Rust → wasm** | Fast. One binary for CLI, LSP and browser. Proven by nanoda_lib (a Rust Lean kernel; [nanoda_lib](https://github.com/ammkrn/nanoda_lib)). oxc/swc parser ecosystem. | Two-language project. The elaborator and tactic framework want rapid iteration and closeness to TS types, which is painful across a wasm boundary. Elaboration, not kernel checking, dominates run time in practice. |
| **Go** | Aligns with tsgo. | ProofScript is *not* inside tsgo (B.1), so the alignment buys little. Weak browser story (large wasm). |
| **Lean as backend** ("translate ProofScript to Lean") | Mature, battle-tested kernel. Mathlib, `omega`, `simp`, `grind`, `bv_decide`. The project owner already has a Lean→wasm pipeline (Lasm), so a Lean kernel could even run in the browser. | Translating JS semantics (floats, mutation, aliasing, exceptions, async, objects, prototype chains) to Lean is the hard part, and that semantics work is needed anyway. If users write tactics, they are writing *Lean* in TS syntax, and error messages and goal states round-trip through a foreign elaborator. Requires a Lean toolchain (GBs) in every JS developer's environment, plus extra latency. Elaboration (implicit arguments, unification, coercions) would run in Lean against generated code that users never see. The "Lean, but TypeScript" identity collapses into "a Lean front end". |

**Recommendation:** own elaborator, tactic engine and kernel in TypeScript, over a core calculus *deliberately compatible with Lean 4's kernel language*: CIC with universes, inductive families and quotients, with proof irrelevance for `Prop`. Add an **exporter to the lean4export format** ([lean4export](https://github.com/TwoFX/lean4export)) so any ProofScript library can be independently re-checked by Lean's own kernel, nanoda_lib or lean4lean. That gives:

- **trust diversity**: two independent kernels, as Lean's own ecosystem uses;
- a path to **import Lean and Mathlib theorems** about pure mathematics, sharing the core-language design;
- no Lean dependency for everyday users.

Note that the lean4export format was in flux in late 2025 (a format fork for nanoda, Mathlib export issues), so target a pinned format version.

SMT-backed automatic discharge of verification conditions (Dafny/Verus style, e.g. Z3 via wasm, which esverify used) is complementary. It produces proof *terms* (preferably) or trusted `smt` axioms that are clearly flagged.

---

## Recommendation

### Syntax strategy

**Hybrid (A.4):**

- `.pts`/`.ptsx` files: TypeScript plus a small, closed, keyword-led, bracket-balanced, **whitespace-erasable** grammar extension.
- ProofScript keywords are reserved in those files.
- Clauses go between the signature and the body for functions, and as leading statements in loop bodies.
- Propositions are TS-flavoured expressions (`===`, `&&`, `forall`, `==>`).
- Dependent types reuse TS's function-type and generic syntax, with value parameters `<n: nat>` and refinements `(x: T) where P`.
- Inductives describe *ghost views* of existing TS runtime shapes (discriminated unions, arrays, classes) and never introduce new runtime representations.
- Proofs come in three forms: recursive term proofs (the default, JS-like), `by { … }` tactic blocks with Lean tactic names, and `calc { … }`.
- Plain `.ts` interop goes through erased `.d.ts` plus `.d.pts` sidecars, with an optional later comment-based "lite" contract mode for unrenamed `.ts` files.

### Tooling architecture

```
.pts source
  └─ ProofScript parser (TS; derived from TS 6 scanner/parser)
       ├─ PS-AST ──► elaborator ──► core terms ──► kernel (TS) ──► diagnostics + goal states
       │               ▲   (queries TS types of runtime exprs via typescript/sync or TS6 API)
       │               │                                   └─► lean4export (optional re-check)
       └─ virtual TS + neutral span map
             ├─► TS 7.1 content mapper adapter (tsc CLI, tsgo LSP, .d.ts emit, proof diagnostics)
             └─► Volar LanguagePlugin adapter (TS 6 fallback: pts-tsc, VS Code, Zed, Neovim)
erase (whitespace-preserving) ──► .ts ──► amaro/oxc strip ──► .js   (pts build / register loader / bundler plugins)
ProofScript LSP side-channel ──► $/proofscript/goals + RPC ──► React infoview webview (+ TSX widgets)
```

### Phased path

1. **Phase 0 — spike (2–4 weeks).**
   - Blanking pre-pass parser for `theorem`, `requires`, `ensures`, `invariant` and `decreases`.
   - `pts strip` (whitespace-preserving).
   - `proofscript/register` Node loader.
   - Vite/esbuild plugins.
   - TextMate grammar.
   - Goal: `.pts` files run everywhere and type-check as TS via `pts-tsc`.
2. **Phase 1 — MVP verifier.**
   - Volar language plugin (TS 6) and a TS 7.1 content mapper sharing one virtual-code generator.
   - Spec expressions mapped verbatim into virtual TS, so rename and hover work.
   - A VC generator for first-order contracts and loop invariants over `int`/`nat`/`bool`/arrays/discriminated unions, discharged by Z3-wasm.
   - Proof errors surfaced as mapper diagnostics.
   - `.d.ts` emit with erased refinements.
   - At this point ProofScript is a "Dafny for TS" that CI can gate on with `tsc --runExternalCode`.
3. **Phase 2 — dependent types and kernel.**
   - The real parser (TS 6 fork).
   - Core calculus and kernel in TS; value-indexed types; `inductive` ghost families; `theorem` with term proofs; termination checking (`decreases`).
   - `.d.pts` sidecars.
   - `sorry` and holes.
   - Goal panel (LSP side-channel plus webview).
4. **Phase 3 — interactive proving.**
   - Tactic framework (`by { … }`), with `intro`, `induction`, `cases`, `simp`, `omega`, `rfl`, `exact`, `calc`, extensible via tactics *written in ProofScript*.
   - Interactive goals with RPC; TSX widgets.
   - tree-sitter grammar.
   - SMT VCs converted into kernel-checkable terms where possible.
5. **Phase 4 — ecosystem and trust.**
   - lean4export exporter and an independent re-check in CI.
   - Standard library of verified JS data structures.
   - Optional boundary contracts.
   - Comment-based lite mode for `.ts`.
   - Rust/wasm kernel if profiling demands it.
   - A long-term effort to verify the ProofScript kernel in ProofScript.

### Syntax sketch — idiomatic ProofScript

```ts
// list.pts
import { omega, simp } from "proofscript/tactics";

export type List<T> =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat
  decreases xs
{
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function append<T>(xs: List<T>, ys: List<T>): List<T>
  ensures r => length(r) === length(xs) + length(ys)   // proved automatically
  decreases xs
{
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

theorem add_comm(a: nat, b: nat): a + b === b + a by { omega }

// value-indexed view over a plain array: erases to `readonly T[]`
export type Vec<T, n: nat> = (xs: readonly T[]) where xs.length === n;

export function zip<A, B, n: nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> {
  const out: [A, B][] = [];
  for (let i = 0; i < xs.length; i++) {
    invariant out.length === i && i <= n;
    out.push([xs[i], ys[i]]);
  }
  return out;
}

export function binarySearch(a: readonly int[], key: int): int
  requires forall (i: nat, j: nat) => i < j && j < a.length ==> a[i] <= a[j]
  ensures r => (r >= 0 ==> a[r] === key) && (r < 0 ==> !a.includes(key))
{
  let lo = 0, hi = a.length;
  while (lo < hi) {
    invariant 0 <= lo && lo <= hi && hi <= a.length;
    invariant forall (i: nat) => (i < lo || (hi <= i && i < a.length)) ==> a[i] !== key;
    decreases hi - lo;
    const mid = lo + ((hi - lo) >> 1);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}

theorem length_append<T>(xs: List<T>, ys: List<T>):
  length(append(xs, ys)) === length(xs) + length(ys)
by {
  induction xs with
  | nil => simp [append, length]
  | cons(h, t, ih) => simp [append, length, ih]; omega
}
```

Erased to TS, which is what `.d.ts` consumers and runtimes see:

```ts
export type List<T> = | { readonly tag: "nil" } | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };
export function length<T>(xs: List<T>): number { return xs.tag === "nil" ? 0 : 1 + length(xs.tail); }
export function append<T>(xs: List<T>, ys: List<T>): List<T> { /* identical body */ }
export type Vec<T, n> = readonly T[];
export function zip<A, B, n>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> { /* identical body, invariants blanked */ }
export function binarySearch(a: readonly number[], key: number): number { /* identical body */ }
```

Value type parameters become phantom type parameters. Theorems vanish.

---

## Sources

- TypeScript blog index: https://devblogs.microsoft.com/typescript/
- Announcing TypeScript 7.0 (no API; `@typescript/typescript6`): https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/
- Announcing TypeScript 7.1 Beta (API entry points; content mappers; Volar): https://devblogs.microsoft.com/typescript/announcing-typescript-7-1-beta/
- typescript-go source: https://github.com/microsoft/typescript-go (`internal/contentmapper`, `internal/spanmap/spanmap.go`, `internal/compiler/emitter.go`, `internal/tsoptions/tsconfigparsing.go`, `internal/parser/parser.go`)
- InfoWorld / Visual Studio Magazine coverage of the TS 7 timeline: https://infoworld.com/article/4100582/microsoft-steers-native-port-of-typescript-to-early-2026-release.html, https://visualstudiomagazine.com/articles/2025/12/02/microsoft-gets-real-on-native-typescript-remake.aspx
- Node.js TypeScript / type stripping docs: https://nodejs.org/api/typescript.html
- Amaro: https://github.com/nodejs/amaro
- TS `erasableSyntaxOnly`: https://www.typescriptlang.org/tsconfig/erasableSyntaxOnly.html
- TC39 Type Annotations proposal: https://github.com/tc39/proposal-type-annotations
- Volar.js docs: https://volarjs.dev/reference/languages/ ; source https://github.com/volarjs/volar.js (`packages/language-core/lib/types.ts`, `packages/source-map/lib/sourceMap.ts`)
- Civet: https://github.com/DanielXMoore/Civet
- Ripple: https://www.ripplejs.com , https://github.com/trueadm/ripple
- tree-sitter-typescript grammar: https://docs.rs/crate/tree-sitter-typescript/latest/source/typescript/grammar.js
- Lean widgets: https://lean-lang.org/doc/api/Lean/Widget/UserWidget.html , https://lean-lang.org/doc/api/Lean/Widget/Types.html ; vscode-lean4 infoview: https://github.com/leanprover/vscode-lean4
- lean4export: https://github.com/TwoFX/lean4export ; nanoda_lib: https://github.com/ammkrn/nanoda_lib ; lean4lean (Carneiro, TYPES 2025): https://drops.dagstuhl.de/storage/00lipics/lipics-vol384-types2025/LIPIcs.TYPES.2025.2/LIPIcs.TYPES.2025.2.pdf
- esverify: https://github.com/levjj/esverify
- Refinement Types for TypeScript (PLDI 2016): https://goto.ucsd.edu/~pvekris/docs/pldi16.pdf , https://ar5iv.labs.arxiv.org/html/1604.02480
- Dafny reference: https://dafny.org/latest/DafnyRef/DafnyRef ; Verus guide: https://verus-lang.github.io/verus/guide/ ; F*: https://fstar-lang.org/tutorial/ ; Idris 2: https://idris2.readthedocs.io ; Liquid Haskell: https://ucsd-progsys.github.io/liquidhaskell/ ; Lean 4: https://lean-lang.org/doc/reference/latest/
