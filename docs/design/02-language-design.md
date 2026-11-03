# ProofScript Language Design

Status: **design draft v0.1** (2026-11-02). Implements the requirements in [01-requirements.md](01-requirements.md) (cited as R1–R22). Synthesizes [research/01–04](../research/).

> **Thesis.** ProofScript is TypeScript plus a *ghost layer*: specifications, theorems, proofs and value-indexed types that live only in erasable positions. The ghost layer elaborates into a small, Lean-4-compatible kernel that is the sole root of trust. Ordinary TypeScript code is untouched; the subset of it that specs mention is *reflected* into the kernel with JavaScript's real semantics. Nothing TypeScript's own type checker concludes is ever trusted by a proof.

## 1. The shape of the language

Three kinds of code coexist in a `.pts` file, distinguished by **mode** (borrowed from Verus, with Idris 2's quantity-0 erasure underneath):

| Mode | What it is | Runs? | Examples |
|---|---|---|---|
| **exec** | Ordinary TypeScript | Yes | functions, classes, statements, every existing TS construct |
| **ghost** | Values and functions that exist only for reasoning | No (erased) | `ghost let`, value type-parameters `<n: nat>`, `inductive` types, ghost functions, spec expressions |
| **proof** | Proofs of propositions | No (erased) | `theorem`, `by { … }`, `proof { … }`, `assert … by`, `calc` |

Exec code may *mention* ghost and proof code only in erasable positions, and ghost/proof code may freely *read* exec code that has been reflected into the logic (§6.2). This mode discipline is what makes R3 (compile = strip) and R4 (proofs never affect runtime) theorems rather than hopes.

A first taste (full worked examples in §11):

```ts
// list.pts
export type List<T> =
  | { readonly tag: "nil" }
  | { readonly tag: "cons"; readonly head: T; readonly tail: List<T> };

export function length<T>(xs: List<T>): nat {
  return xs.tag === "nil" ? 0 : 1 + length(xs.tail);
}

export function append<T>(xs: List<T>, ys: List<T>): List<T> {
  return xs.tag === "nil" ? ys : { tag: "cons", head: xs.head, tail: append(xs.tail, ys) };
}

theorem length_append<T>(xs: List<T>, ys: List<T>):
  length(append(xs, ys)) === length(xs) + length(ys)
by {
  induction xs;
  simp [length, append];
}
```

Stripped, this is exactly the TypeScript a developer would have written (`nat` becomes `number`; the theorem becomes blank lines).

## 2. Architecture overview

```
                 ┌──────────────────────────── untrusted ─────────────────────────────┐
 .pts source ──► │ parser ──► elaborator ──► tactics / decision procedures / SMT      │
                 │   │            │  (uses tsc only for exec-code typing hints)       │
                 │   │            ▼                                                   │
                 │   │      kernel terms + obligations                                │
                 └───┼────────────┼───────────────────────────────────────────────────┘
                     │            ▼
                     │    ┌───────────────┐  export  ┌──────────────────────────────┐
                     │    │ KERNEL (TCB)  │ ───────► │ independent re-check (Lean 4 │
                     │    │ LeanTT in TS  │          │ kernel, nanoda, lean4lean…)  │
                     │    └───────────────┘          └──────────────────────────────┘
                     ├──► strip (syntactic, whitespace-preserving) ──► .ts ──► .js
                     └──► declaration view (semantic) ──► tsc / TS 7.1 content mapper,
                                                        .d.ts + .d.pts, editor features
```

Logical layers (from [research/03 §9](../research/03-foundations-and-soundness.md)):

- **K — Kernel.** Lean 4's type theory: dependent functions, universe polymorphism, inductive families, impredicative proof-irrelevant `Prop`, quotients, `propext`. Classical choice only in erased positions. Small (target: a few thousand lines of TypeScript), and every proof exportable to Lean's kernel export format for independent re-checking (R15).
- **M — JavaScript model.** Inside the kernel: `JSVal`, IEEE-754 `Float64`, UTF-16 strings, `Int` for BigInt, and (from phase 3) a deep-embedded semantics of a verifiable JS subset **S**.
- **P — Pure fragment.** TypeScript functions that are pure and total are reflected as kernel definitions (§6.2).
- **I — Imperative verification.** Contracts, loop invariants and frames for code with local and heap mutation, verified by weakest preconditions proved sound against M (§8).
- **B — Boundaries.** Values and functions from unverified code are opaque; knowledge enters only through verified validators, user-written runtime checks, or tracked `assume` specs (§8.4).
- **E — Environment assumptions.** Stated once, listed in every trust footprint (§6.7).

## 3. Files, modules and interop

- **`.pts` / `.ptsx`** are ProofScript source, the analogue of `.ts`/`.tsx`. Opting in is renaming a file (R11). A `.pts` file with no specs is exactly a `.ts` file (R10).
- **`.d.pts`** files are spec sidecars, the analogue of `.d.ts`. They carry the ghost layer of a module's public surface: contracts, reflected definitions, exported theorems, value-indexed types. Generated automatically for `.pts` modules; hand-written for third-party code, where their contents are **assumptions** (R13, R16).
- **Imports are ordinary ES imports** (R7). `.pts` imports `.ts`/`.js` modules; `.ts` imports `.pts` modules and sees plain `.d.ts` types (refinements erased to carriers, theorems absent).
- **Publishing:** a package ships `.js` + `.d.ts` as today, plus `.d.pts` (and optionally `.pts` sources and proof certificates). Plain TS consumers notice nothing.
- **Configuration** lives in `tsconfig.json` under `"proofscript": { … }` (assurance level, axioms allowed, solver budget, `noEmitOnProofError`).

## 4. Types

### 4.1 TypeScript types are documentation, kernel types are truth

`tsc` keeps checking `.pts` code exactly as it would check `.ts` (R18), through the declaration view (§10). Its verdicts are *never* used by proofs (R17). Instead, the elaborator **interprets** a well-behaved fragment of TypeScript types as kernel types:

| TypeScript | Kernel interpretation |
|---|---|
| `boolean`, `true`, `false` | `Bool`, singletons |
| `number` | `Float64` (bit-exact IEEE-754 binary64 with ECMAScript's operations, one NaN, ±0, ±∞) |
| `bigint` | `Int` |
| `string`, string literal types | `JSString` (sequence of UTF-16 code units), singletons |
| `undefined`, `null` | unit constructors of `JSVal` |
| literal types `3`, `"a"` | subtypes `{ x // x = 3 }` |
| readonly record types | structures |
| discriminated unions of readonly records (recursive allowed if strictly positive) | **inductive types** |
| tuples, `readonly T[]` | products, immutable sequences |
| `T \| undefined` (non-overlapping unions) | sums |
| generic `T` | universe-polymorphic type variable |
| `(x: A) => B` | in the pure fragment, a kernel function (only for functions known pure and total); otherwise an opaque behaviour |
| `any`, `unknown`, anything not in this table (conditional/mapped/template types beyond simple cases, classes until phase 4) | **`JSVal`** — no information |

The rule "anything else is `JSVal`" is what makes this sound: a type ProofScript cannot interpret honestly contributes nothing.

### 4.2 ProofScript prelude types

Available in every `.pts` file without import (each erases to its TS carrier):

| Type | Meaning | Erases to |
|---|---|---|
| `int` | `number` that is a safe integer (`Number.isSafeInteger`) | `number` |
| `nat` | `int` that is `>= 0` | `number` |
| `Int`, `Nat` | mathematical integers (ghost only) | — |
| `Rat` | rationals (ghost only) | — |
| `Prop` | the universe of propositions | — |
| `Type` | the universe of types | — |

`int` and `nat` are **proved refinements**, never assumptions (R19): a value gets type `int` only if the checker proves it is a safe integer.

### 4.3 Refinement types

```ts
type Pos = (x: number) where x > 0;
type Percent = (p: int) where 0 <= p && p <= 100;
type SortedArray = (a: readonly int[]) where isSorted(a);
```

A refinement is a kernel subtype `{ x : T // P x }`; its runtime representation is the carrier value itself (proof erased, like Lean's `Subtype`). Strip turns `(x: number) where x > 0` into `number` (whitespace-padded). Liquid-style `{v: T | p}` is rejected because it collides with TS object types.

### 4.4 Value-indexed (dependent) types

Value parameters go **in generic parameter lists**, which TypeScript already erases. A parameter with a `:` annotation instead of `extends` is a value parameter:

```ts
type Vec<T, n: nat> = (xs: readonly T[]) where xs.length === n;
type Fin<n: nat> = (i: nat) where i < n;

function zip<A, B, n: nat>(xs: Vec<A, n>, ys: Vec<B, n>): Vec<[A, B], n> { … }
function replicate<T>(n: nat, x: T): Vec<T, n> { … }          // depends on a runtime parameter
function get<T, n: nat>(xs: Vec<T, n>, i: Fin<n>): T { return xs[i]; }  // no bounds check needed
```

- Value arguments are almost always **inferred** (like Lean's implicit arguments). Explicit ones are written `zip<A, B, 3>(…)` and erased with the other type arguments.
- `(x: A) => B` where `B` mentions `x` is a dependent function type (Π).
- **Exec functions never take ghost value *arguments*** in their runtime parameter lists. Ghost information flows through value type-parameters and `requires` clauses (discharged at the call site, Dafny-style). This keeps call sites strippable without marking ghost arguments (R3).

**Unified syntax, sort-directed elaboration.** In a dependent language, types and terms are the same grammar. In `.pts` type positions, ProofScript accepts the union of the TS type grammar and a pure-expression grammar (`n + 1`, `length(xs)`, `xs.length`, `&&`, `===`). The elaborator decides by expected sort whether a node is a type or a value. Where the TS grammar already assigns a meaning (`A | B`, `{ a: T }`, `typeof x`, `X extends Y ? A : B`), the TS meaning wins (R2). Name resolution follows the same rule: a type-position identifier resolves to a *type* if one is in scope (TS meaning), otherwise to a *value* (ProofScript meaning, where TS would have reported "cannot find name").

### 4.5 Inductive types

Two forms, with **no new runtime representations ever**:

1. **Runtime data = TypeScript discriminated unions.** A recursive discriminated union of readonly records (like `List<T>` above) is recognized as an inductive type automatically. Pattern matching is TS's own: `switch (xs.tag)` and `if (xs.tag === "nil")`, and **TypeScript's control-flow narrowing is elaborated into dependent pattern matching** (the motive is inferred from the narrowed branches).
2. **Ghost inductive families** for propositions and indexed types used only in reasoning:

```ts
inductive Even<n: nat>: Prop {
  zero: Even<0>;
  step<k: nat>(h: Even<k>): Even<k + 2>;
}
```

`inductive` declarations erase completely. Non-`Prop` ghost inductives are allowed (e.g. syntax trees for a verified interpreter's spec) but have no runtime form; to compute with data, declare it as a TS union.

## 5. Erasure

### 5.1 Ghost positions

A construct is erasable iff it is in a **ghost position** ([research/03 §7.2](../research/03-foundations-and-soundness.md)):

- **G1 Sort positions:** type annotations, generic parameters/arguments (including value parameters), type aliases, interfaces.
- **G2 Proof positions:** any term whose type is a `Prop`: theorems, `by` blocks, `proof { }` blocks, `assert`, `calc`, `decreases` measures.
- **G3 Ghost bindings:** `ghost let`/`ghost const`, ghost functions, `inductive` types; a ghost variable may be used only in G1–G3 positions (QTT quantity 0, checked).
- **G4 Elimination restriction:** exec code may branch only on runtime-relevant values. A proof may be eliminated into exec code only if its type is a syntactic subsingleton (Lean's rule).
- **G5 Parametricity:** no runtime inspection of erased types (TS already forbids this).
- **G6 Noncomputable axioms** (classical choice) only in G1–G3.

### 5.2 The strip pass

`strip` is a syntactic, single-file pass (R3) that replaces with spaces (keeping newlines):

- ProofScript declarations (`theorem`, `inductive`, `ghost function`, `axiom`) and statements (`ghost let`, `proof { }`, `assert …;`, loop `invariant`/`decreases`);
- function clauses (`requires`, `ensures`, `decreases`, `reads`, `modifies`, `throws`);
- refinement syntax (`(x: T) where P` → `T`);
- the `: nat` of value parameters (`<n: nat>` → `<n>`, so later references to `n` in type positions remain valid TS type-parameter references);
- value arguments that are not TS type syntax (`Vec<T, n + 1>` → `Vec<T, any>`);
- prelude types `int`/`nat` → `number`.

**Erasure correctness** has two halves: (i) syntactically, `emit(M)` equals the JS that stock TS type-stripping produces from `strip(M)`, checked on every build by diffing against an independent stripper; (ii) semantically, the kernel's erasure of the elaborated module corresponds to `strip(M)` (the MetaCoq-style erasure theorem; [research/03 §7](../research/03-foundations-and-soundness.md)).

## 6. The logic

### 6.1 Propositions and booleans

`Prop` is the kernel's proof-irrelevant universe. Spec expressions (in `requires`, `ensures`, `invariant`, `where`, theorem statements) are written as ordinary TypeScript expressions and lifted to `Prop`:

- A `boolean`-valued expression `b` means the proposition `b = true`. So spec meaning and runtime meaning of `x < y`, `s.startsWith(p)`, `isSorted(a)` coincide by construction. Spec/code divergence is a top pitfall in prior art ([research/02](../research/02-verification-prior-art.md)); this rule avoids it.
- On propositions, `&&`, `||`, `!` mean ∧, ∨, ¬, and two operators are added in spec positions only: `==>` (implication) and `<==>` (iff). Neither token sequence is valid JS, so they reinterpret nothing (R2).
- Quantifiers are **ordinary ghost functions taking lambdas** (no new syntax): `forall((i: nat) => P)`, `exists((x: T) => P)`. They are imported from the prelude.
- **Equality.** `===` keeps its JavaScript meaning everywhere (including `NaN !== NaN` and reference identity on objects). Propositional equality is `eq(a, b)` (kernel `Eq`). For `int`, `nat`, `bigint`, `boolean` and `string`, the prelude proves `(a === b) <==> eq(a, b)`, so the two can be used interchangeably on those types.

### 6.2 Reflection: when exec code becomes logic

A TypeScript function may be mentioned inside a spec or proof only if it is **reflectable**: then the elaborator translates it into a kernel definition (Liquid Haskell's refinement reflection, Dafny's functions, Verus's spec fns), so that the spec talks about *the very function that runs*. A function is reflectable when:

1. **Pure:** no reads or writes of mutable state outside its own locals; no calls to unreflectable functions. Local `let` mutation and loops *are* allowed: they are translated through a state-passing encoding, as Lean's `do`-notation with `mut` variables is pure.
2. **Total:** every recursion is structural on an inductive argument, or has a `decreases` measure the checker proves. Loops need a `decreases` measure, inferred where possible.
3. **Within the interpreted type fragment** (§4.1) for its parameters and result.
4. **Non-throwing** on inputs satisfying its `requires`, or explicitly typed with an exception result (later).

Functions that are verified against contracts but not reflectable (imperative, effectful, possibly non-terminating) are still fully verifiable (§8); they just cannot appear *inside* other specs. Unverified functions are never reflected and never become kernel equations (R20).

**Trust of reflection.** In phase 1 the reflection translation is trusted (as in Dafny and Verus) and listed in the trust footprint as `reflection`. From phase 3, the emitted JS is re-parsed by a small independent parser into the deep-embedded subset S, and a generic **adequacy theorem** proves the reflected definition agrees with the JS semantics, up to resource exhaustion (CakeML's theorem shape). Reflection then leaves the TCB.

### 6.3 Numbers

ProofScript is honest about JavaScript numbers (R19), with arithmetic semantics **directed by static type**, Verus-style:

| Operand types | In exec code | In spec code |
|---|---|---|
| `number` | IEEE-754 binary64, as JS | IEEE-754 binary64, as JS (same meaning) |
| `int`, `nat` | IEEE-754, **plus an obligation that the result is exact** (safe-integer range for `+ - *`; for `/`, either exactness or the result is typed `number`) | exact integer arithmetic (`Int`) |
| `bigint` | exact integer, as JS | exact integer (same meaning) |
| `Int`, `Nat`, `Rat` | not allowed (ghost) | exact mathematical arithmetic; `/` on `Int` yields `Rat` |

So `theorem add_comm(a: int, b: int): a + b === b + a` is a theorem about integers, and `function add(a: int, b: int): int { return a + b; }` incurs the obligation `|a + b| ≤ 2⁵³ − 1`, the integer-overflow check verification languages are known for. The exec/spec agreement on `int` is not an assumption: it is the theorem "binary64 operations on safe integers whose exact result is safe are exact", proved once in the prelude.

`Math.sin`, `Math.exp` and other operations the ECMAScript spec calls *implementation-approximated* are uninterpreted, constrained only by the spec's guarantees. Bitwise operators go through `ToInt32`/`ToUint32` and are modelled as 32-bit operations.

### 6.4 Strings, arrays, objects

- `string` is a sequence of UTF-16 code units; `length` and indexing are code-unit based, matching JS. Locale- and ICU-dependent operations (`toLowerCase`, `localeCompare`, `normalize`) are uninterpreted.
- `readonly T[]` is an immutable sequence in the pure fragment. `a[i]` has type `T | undefined` in general, exactly as at runtime; it has type `T` where `0 <= i < a.length` is provable (an automatic well-formedness obligation in spec positions).
- Mutable arrays, `Map`, `Set` and objects with identity live in the heap model used by imperative verification (§8).
- Implicit coercions that can run user code (`ToPrimitive` on objects, `==`) are outside the verifiable subset; using them in verified code is a verification error, never a TS error.

### 6.5 Termination

Reflected functions and theorems must terminate: structural recursion is detected automatically; otherwise `decreases e` (a `nat`, a tuple compared lexicographically, or a well-founded relation). Verified-but-unreflected functions also prove termination by default; `decreases *` opts into partial correctness, as in Dafny. Possibly divergent code is modelled as a least fixpoint in the program logic, never as a pure kernel function, so it cannot introduce inconsistency (R20).

### 6.6 Assumptions and consistency

Three mechanisms admit unproved facts, all tracked (R16):

- **`admit`** — a proof hole (Lean's `sorry`). Usable anywhere a proof is expected.
- **`assume` specs** — contracts on *unverified* code, usually in `.d.pts` files:

  ```ts
  // lodash.d.pts
  assume declare function sortBy<T>(xs: readonly T[], key: (x: T) => number): T[]
    ensures r => isPermutation(r, xs) && isSortedBy(r, key);
  ```

  Because unverified functions are never kernel functions, an `assume` spec is a predicate on an *external behaviour*, not an equation between kernel terms. It cannot make the logic inconsistent: a false assumption makes conclusions that depend on it vacuous, not `False` provable. The checker can additionally ask for a satisfiability witness.
- **`axiom`** — a raw kernel axiom. Can make the logic inconsistent; disabled unless `"allowAxioms": true`, and always printed by `proofscript audit`.

### 6.7 Trust footprints

Every theorem and verified declaration has a **trust footprint**: the standard kernel axioms used (`propext`, `Quot.sound`, `Classical.choice`), every `admit`, `assume` and `axiom` it transitively depends on, uncertified solver results (§10.3), `reflection` (until phase 3), and the environment assumptions:

- **E1** built-in intrinsics are not tampered with (e.g. the app runs under SES `lockdown()`, or verified code uses captured primordials);
- **E2** verified mutable state is not aliased by unverified code;
- **E3** the JS engine implements the verifiable subset as specified;
- **E4** no shared-memory concurrency with verified state;
- **E5** resource exhaustion (stack overflow, out of memory) may happen at any call.

`proofscript audit` prints footprints per declaration, per module and per package (transitively through dependencies' `.d.pts`).

## 7. Concrete syntax

### 7.1 The no-reinterpretation rule

Every new construct is introduced by a **contextual keyword** and recognized **only where the same tokens could not be valid TypeScript** (R2), using the same techniques TypeScript used for `type`, `declare`, `abstract` and `satisfies`:

1. **No line terminator** between the keyword and the next token. `theorem foo(...)` on one line is a ProofScript theorem; `theorem` followed by a newline is an ordinary identifier expression (ASI).
2. **The next token must not continue an expression.** `assert x > 0;` is a ghost assertion, but `assert(x > 0)`, `assert.ok(…)`, `assert = …` are ordinary TypeScript, because they are valid TS. Likewise `invariant(cond, msg)` (a common React-ecosystem helper) remains a runtime call. If a keyword-led form is *intended* but resolves to a runtime call, the checker lints it; and a runtime assertion function with an `assume`/verified spec (e.g. `node:assert`) also yields its condition as a proof fact afterwards, which is sound because it throws otherwise.
3. **Clauses occupy positions where TS allows nothing**: between a function's signature and its body; after a type alias's carrier; the leading statements of a loop body.
4. **Spec-only operators** (`==>`, `<==>`) are recognized only inside spec positions, and are not valid TS token sequences anywhere.

### 7.2 Declarations

```ts
theorem name<Params>(binders): Proposition by { tactics }   // tactic proof
theorem name<Params>(binders): Proposition { statements }   // term proof: a ghost function returning a proof
inductive Name<Indices>: Prop { ctor: Type; … }             // ghost inductive family
ghost function f(…): T { … }                                // ghost-only function (may use Int, Rat, Prop, …)
assume declare function f(…): T requires … ensures …;      // trusted spec of unverified code
axiom name(binders): Proposition;                           // raw axiom (off by default)
```

A theorem is a ghost function whose return type is a proposition (Curry–Howard). Its binders are universally quantified; `theorem t(x: nat): P(x)` states ∀ x : ℕ, P x. Theorems are exported and imported like any declaration.

### 7.3 Function clauses

```ts
function f<T, n: nat>(a: A, b: B): R
  requires P(a, b)                 // precondition (checked at every verified call site)
  ensures r => Q(a, b, r)          // postcondition on normal return (binder optional)
  decreases m(a)                   // termination measure (or `decreases *`)
  reads a                          // frames (heap-touching code, §8)
  modifies b
  throws e => E(e)                 // exception spec; omitted = may throw (phase 1)
{ … }
```

The same clauses attach to methods, arrow functions (`(x: int): int requires x > 0 => …`), and overload-free function expressions.

### 7.4 Statements

```ts
ghost let total0 = total;                 // ghost variable
assert lo <= mid && mid < hi;             // ghost assertion (discharged automatically)
assert sorted(a) by { simp [sorted]; };   // assertion with explicit proof
proof { lemma_sum_split(a, i); }          // ghost block: call lemmas, case-split, …
while (lo < hi) {
  invariant 0 <= lo && lo <= hi && hi <= a.length;
  decreases hi - lo;
  …
}
```

### 7.5 Proofs

Three styles, freely mixed. Most proofs should need none of them: automation (`omega`-style arithmetic, simplification, SMT) discharges routine obligations.

- **Tactic blocks** `by { … }`: brace-delimited, `;`-separated, Lean tactic names (`intro`, `induction`, `cases`, `simp`, `omega`, `rfl`, `exact`, `apply`, `rw`, `calc`, `decide`, `grind`), so that Lean users and LLMs trained on Lean/Mathlib transfer directly. Tactics are untrusted programs that produce kernel terms; in later phases they are written in ProofScript itself.
- **Term proofs** as recursive functions, the most JS-native style (proof by induction = recursion, case analysis = `switch`):

  ```ts
  theorem length_append<T>(xs: List<T>, ys: List<T>):
    length(append(xs, ys)) === length(xs) + length(ys)
  {
    switch (xs.tag) {
      case "nil":  return rfl;
      case "cons": return congrArg((n: nat) => n + 1, length_append(xs.tail, ys));
    }
  }
  ```

- **`calc` chains**:

  ```ts
  calc {
    sum(append(xs, ys));
    === sum(xs) + sum(ys)   by { simp [sum_append] };
    === sum(ys) + sum(xs)   by { omega };
  }
  ```

## 8. Verifying imperative TypeScript

### 8.1 Local mutation

Functions whose effects are confined to local variables (and fresh, non-escaping arrays and objects) are verified by weakest-precondition VC generation over a state-passing translation. Loops need `invariant`s (some are inferred). This covers most algorithmic code.

### 8.2 The heap

Code that mutates parameters or shared objects uses **dynamic frames**, as in Dafny: `reads`/`modifies` clauses name the objects and arrays a function may touch, and `old(e)` refers to pre-state values in `ensures`. Underneath, this is a separation-logic program logic proved sound against the JS model (Iris-style), but users see only frames, as Dafny users do. Separation-logic notation is available to experts for callbacks and ownership transfer. Classes are modelled as records with a fixed prototype; getters/setters, `Proxy` and prototype mutation are outside the verifiable subset.

### 8.3 Async and callbacks

Phase 4. `async`/`await` is modelled with an event-loop job queue; specs about interleavings use invariants. Until then, a verified function that awaits or invokes unverified callbacks gets no guarantees about state those may touch (they are havocked).

### 8.4 Boundaries with unverified code

Values from unverified code (`.ts`/`.js` modules, `any`, `JSON.parse`, the network) have kernel type `JSVal`, whatever their TS type says (R17). Exec code can use them freely; ProofScript never restricts what programs do (R10), only what can be proved. Knowledge enters through one of:

1. **Verified validators**: an ordinary TS function `parseFoo(x: unknown): Foo | undefined` with a verified `ensures r => r !== undefined ==> valid(r)`. Validators should copy-in (build a fresh value), so later mutation by the producer cannot invalidate the fact. ProofScript can generate them from types (as zod/io-ts do), as committed, visible TS code.
2. **User-written runtime checks**: `if (typeof x === "number" && x > 0)` narrows the logic just as it narrows TS types, but soundly.
3. **`assume` specs** (§6.6), tracked.

A verified function with a `requires` clause that is exported to unverified callers has no guarantee its precondition holds; `audit` lists such "boundary preconditions" so the user can decide whether to add an explicit runtime check.

## 9. Assurance levels and adoption

A project or module selects a level in `tsconfig.json` (R12). Each is a superset of the obligations of the previous one.

| Level | Name | What is checked |
|---|---|---|
| 0 | **script** | Nothing beyond TypeScript. `.pts` = `.ts`. Specs are parsed and type-checked as documentation. |
| 1 | **contracts** | Every written spec, theorem and refinement is verified. `admit` and `assume` allowed. |
| 2 | **sound** | Level 1, plus implicit safety obligations in verified functions: `int` overflow, in-bounds indexing where the result is used at its TS type, termination. |
| 3 | **audited** | Level 2, plus no `admit`, no `axiom`; every `assume` must be in a reviewed `.d.pts`; solver results must be certified by the kernel. |
| 4 | **complete** | Level 3, plus every exported function has a spec and boundary preconditions are runtime-checked. |

The adoption path mirrors TypeScript's: rename one file, write one `ensures`, and get value immediately, without touching the rest of the codebase.

## 10. Tooling architecture

### 10.1 Front end

- **Written in TypeScript**, runs in Node and the browser (dogfoodable; the kernel can eventually be verified in ProofScript itself).
- **Parser** derived from the TypeScript 6 parser (the last JS implementation, now frozen), extended with the §7 grammar. A whitespace-blanking `strip` mode is the first deliverable.
- **Elaborator**: bidirectional, with unification for implicit value parameters, elaboration of TS narrowing into dependent pattern matching, and reflection (§6.2).
- **Kernel**: LeanTT type checker in TypeScript, kept deliberately small, with an exporter to Lean 4's kernel export format so every release (and optionally every CI run) is re-checked by independent kernels (R15).

### 10.2 TypeScript integration

- The front end produces a **declaration view**: type-valid virtual TypeScript with span mappings back to the `.pts` source (spec expressions are mapped verbatim so hover, rename and go-to-definition work across code and specs).
- **Primary adapter: TypeScript 7.1 content mappers**, which let `tsc` and the TS language server consume `.pts` through an external process that returns generated TS, mappings and extra diagnostics. Proof errors then appear in plain `tsc` output and CI is `tsc` (R8, R14). (The 7.1 API is in beta; this must be verified by the phase-0 spike.)
- **Fallback adapter: Volar.js** on TypeScript 6, the architecture Vue, Astro, MDX and Svelte use.
- **Build**: `proofscript build`, a Node loader (`node --import proofscript/register`), and Vite/esbuild/Bun/Rollup plugins, all running the syntactic strip followed by the host's normal TS handling.
- **`proofscript eject`** writes the declaration view as plain `.ts` files: leaving ProofScript is as easy as leaving TypeScript.

### 10.3 Automation and the trust boundary

Decision procedures (linear arithmetic, `omega`-style integer arithmetic, simplification, congruence closure) are implemented as tactics that **produce kernel terms**. An SMT solver (Z3/cvc5 compiled to wasm) is used as an untrusted oracle: its answers are either reconstructed as kernel proofs (from unsat cores and proof certificates, an established line of work) or, until reconstruction covers a theory, recorded in the trust footprint as `smt`. Level 3 forbids uncertified `smt`. This prevents a "fast but trusted" path that later has to be ripped out.

### 10.4 Editor experience

A ProofScript LSP side-channel provides a Lean-infoview-style **goal panel** (current hypotheses and goal at the cursor, inside `by` blocks and at any obligation), plus machine-readable goal states. Those serve humans and AI agents equally; AI-written proofs are a first-class workflow, since every proof is kernel-checked regardless of who wrote it.

## 11. Worked examples

### 11.1 Theorem proving

```ts
// nat.pts — pure mathematics, no runtime code at all (erases to an empty module)
inductive Le<n: nat, m: nat>: Prop {
  refl<n: nat>: Le<n, n>;
  step<n: nat, m: nat>(h: Le<n, m>): Le<n, m + 1>;
}

theorem le_trans<a: nat, b: nat, c: nat>(h1: Le<a, b>, h2: Le<b, c>): Le<a, c> by {
  induction h2;
  case refl => exact h1;
  case step(h, ih) => exact Le.step(ih);
}

theorem sum_formula(n: nat): 2 * sumTo(n) === n * (n + 1) by {
  induction n;
  simp [sumTo];
  omega;
}

ghost function sumTo(n: Nat): Nat {
  return n === 0 ? 0 : n + sumTo(n - 1);
}
```

### 11.2 Verifying an existing function

```ts
// search.pts
export function binarySearch(a: readonly int[], key: int): int
  requires forall((i: nat, j: nat) => i < j && j < a.length ==> a[i] <= a[j])
  ensures r => (r >= 0 ==> a[r] === key) && (r < 0 ==> !a.includes(key))
{
  let lo = 0, hi = a.length;
  while (lo < hi) {
    invariant 0 <= lo && lo <= hi && hi <= a.length;
    invariant forall((i: nat) => (i < lo || (hi <= i && i < a.length)) ==> a[i] !== key);
    decreases hi - lo;
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
```

(The common idiom `lo + ((hi - lo) >> 1)` would *fail* to verify here: `>>` truncates through `ToInt32`, so for arrays longer than 2³¹ − 1 elements `mid` goes negative. The checker reports the unprovable `0 <= mid` and the user either adds `requires a.length < 2 ** 31` or uses `Math.floor`. This is the kind of bug ProofScript exists to catch.)

After `strip` (blank lines elided here):

```ts
export function binarySearch(a: readonly number[], key: number): number
{
  let lo = 0, hi = a.length;
  while (lo < hi) {
    const mid = lo + Math.floor((hi - lo) / 2);
    if (a[mid] < key) lo = mid + 1;
    else if (a[mid] > key) hi = mid;
    else return mid;
  }
  return -1;
}
```

### 11.3 A boundary

```ts
// config.pts
import { readFileSync } from "node:fs";

type Port = (p: int) where 1 <= p && p <= 65535;

function parsePort(x: unknown): Port | undefined
  ensures r => r === undefined || (1 <= r && r <= 65535)
{
  return typeof x === "number" && Number.isInteger(x) && x >= 1 && x <= 65535 ? x : undefined;
}

export function loadPort(path: string): Port {
  const raw: unknown = JSON.parse(readFileSync(path, "utf8")).port;  // JSVal: nothing known
  return parsePort(raw) ?? 8080;                                      // proved: a valid Port
}
```

## 12. Open design questions

These are the decisions the design does not yet settle. Each will be resolved by a short design note in `docs/design/` before the code that depends on it.

1. ~~**Kernel strategy.**~~ **Decided (2026-11-02):** our own LeanTT kernel in TypeScript, with every proof exported to and re-checked by Lean in CI.
2. **Lean interop as a library source.** Because the kernel is LeanTT, Lean's core library, and eventually Mathlib, could in principle be imported as kernel terms and re-checked. This could give ProofScript a large mathematical library for free; the cost is mapping Lean's names, notation and type classes into ProofScript surface syntax.
3. **Type classes / overloading of spec operators** (e.g. `+` on user types, `Decidable`). Lean relies on type classes heavily; TS has no direct equivalent. Likely: a ghost `instance` mechanism resolved by the elaborator.
4. **Exception specs by default.** Phase 1 says "may throw" unless specified; level 2 may require `throws` clauses on verified functions.
5. **Heap reasoning surface.** Dynamic frames (Dafny) vs. ownership-flavoured permissions (Verus/Prusti), given that TS has no ownership types.
6. **Classes, `this`, prototypes, getters** in the verifiable subset.
7. **Tactic metaprogramming** — tactics written in ProofScript, with a quotation syntax for kernel terms.
8. **Surface syntax and file extension.** See [04-surface-syntax.md](04-surface-syntax.md), which proposes valid TypeScript (`.ts` + `//@` annotations + `.proof.ts` proof modules) as the primary surface, with this document's dedicated syntax as optional later sugar. Original question: `.pts`/`.ptsx` (recommended; content mappers cannot claim `.ts`) vs. `.proof.ts`, and a comment-based "lite" mode for unrenamed `.ts` files.
