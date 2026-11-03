# ProofScript ↔ Lean 4 Correspondence

Status: **design note v0.1** (2026-11-02).

Goal: ProofScript should *behave* like Lean 4 (same logic, same proof workflow, same tactic vocabulary, same interactive experience) while being written in TypeScript. A Lean user should be able to translate a development line by line, and an LLM trained on Lean and Mathlib should transfer directly.

The kernel is Lean's type theory ([04 §1](04-surface-syntax.md#1-is-it-basically-leans-type-system)), so the correspondence is exact at the level of logic. This table covers the surface.

## Declarations

| Lean 4 | ProofScript (TypeScript) |
|---|---|
| `def f (x : Nat) : Nat := …` | `function f(x: nat): nat { … }`, reflected into the logic when pure and total |
| `def` with structural recursion | recursive function; structural recursion detected automatically |
| `termination_by e` / `decreasing_by` | `e satisfies Decreases;` at the top of the body or loop |
| `partial def` | an ordinary function the checker can't prove terminating: still runs, never enters the logic |
| `noncomputable def` | a ghost function: may use `Nat`, `Int`, `Prop`, classical choice; must never be called at runtime (checked) |
| `theorem name (x : α) : P := by tac` | `function name(x: α): Proof { return prove(P, by(tac)); }` |
| `theorem` whose statement is an inductive `Prop` | `function name(…): Even<Plus<a, b>> { return by(…); }` (statement as return type) |
| `lemma` (Mathlib) | same as `theorem` |
| `example : P := …` | an unexported theorem function (with `noUnusedLocals`, export it or prefix the file with a ProofScript lint override) |
| `@[simp] theorem` | return type `Proof & Simp` |
| other attributes (`@[ext]`, `@[induction_eliminator]`, …) | further marker types intersected into the return type |
| `axiom` | `axiom<P>()` declarations, disabled by default, always reported |
| `sorry` | `sorry` |
| `inductive T \| a \| b (x : T)` (data) | a discriminated union type of readonly records |
| `inductive Even : Nat → Prop` (indexed family) | `interface Even<n extends nat> extends Prop` + `declare namespace Even { function zero(): Even<0>; … }` |
| `structure Point where x : Float` | `interface Point { readonly x: number }` or a readonly object type |
| subtype `{ x : Nat // x < n }` | `nat & Lt<n>` |
| `Fin n`, `Vector α n` | `nat & Lt<n>`, `readonly T[] & Length<n>` |
| `Prop`, `Type`, `Sort u` | `Prop`, `Type`; universe levels inferred |
| implicit arguments `{n : Nat}` | type parameters `<n extends nat>`, inferred at call sites |
| instance-implicit `[Decidable p]` | open question: type classes (see [06](06-decision-log.md)) |
| `namespace X` / `open X` / `section` | ES modules and imports |
| `variable (n : Nat)` | function parameters or generics (no file-level variables) |
| `import Mathlib.X` | `import { … } from "…"`; Lean library import is a later phase |
| `#check e` | hover in the editor (shows the ProofScript type, not just the TS one) |
| `#eval e` | run it: it is TypeScript |
| `#print axioms t` | `proofscript audit t` |

## Proofs

| Lean 4 | ProofScript |
|---|---|
| `by tac₁; tac₂` / newline-separated tactics | `by(tac1, tac2)` |
| `intro x` | `intro("x")` or callbacks (below) |
| `exact e`, `apply e`, `refine e` | `exact(e)`, `apply(e)`, `refine(e)` |
| `rfl`, `decide`, `omega`, `simp [l₁, l₂]`, `simp_all`, `norm_num`, `ring`, `linarith`, `grind` | `rfl`, `decide`, `omega`, `simp(l1, l2)`, `simp_all`, `norm_num`, `ring`, `linarith`, `grind` (implemented progressively) |
| `rw [h]`, `rw [← h]` | `rw(h)`, `rw(rev(h))` |
| `induction xs with \| nil => t₁ \| cons h t ih => t₂` | `induction(xs, { nil: () => t1, cons: (h, t, ih) => t2 })`: hypotheses are callback parameters, so they are real TS bindings |
| `cases h with …` | `cases(h, { … })` |
| `have h : P := proof` | `const h = have(P, proof);` inside a term proof, or `have(P, proof)` as a tactic |
| `calc a = b := p₁ _ = c := p₂` | `calc(a, [b, p1], [c, p2])` |
| `show P` | `show(P)` |
| `constructor`, `left`, `right`, `exists w` | `constructor`, `left`, `right`, `use(w)` |
| term-mode proof by recursion | a recursive theorem function: induction is recursion, case analysis is `switch`/`?:` |
| `fun x => …` proof terms | arrow functions |
| `⟨a, b⟩` anonymous constructors | `and(a, b)`, `exists(w, h)` |

## Statements

| Lean 4 | ProofScript |
|---|---|
| `a = b` | `a === b` on numbers, strings, booleans and bigints (proved equivalent to `eq`); `eq(a, b)` in general |
| `a ≠ b` | `a !== b` |
| `p ∧ q`, `p ∨ q`, `¬p`, `p → q`, `p ↔ q` | `p && q`, `p \|\| q`, `!p`, `implies(p, q)`, `iff(p, q)` |
| `∀ x, P x` | theorem parameters, or `forall((x: T) => P(x))` |
| `∃ x, P x` | `exists((x: T) => P(x))` |
| `∀ i < n, P i` (bounded) | `xs.every(…)` / a `for` loop in a predicate: ordinary TS with its JS semantics |
| `Nat`, `Int` arithmetic | `nat`/`int` in specs mean exact integers; at runtime, operations on them carry no-overflow obligations ([design §6.3](02-language-design.md#63-numbers)) |
| `Float` | `number` (IEEE-754 binary64, bit-exact, as JavaScript) |

## Tooling

| Lean 4 | ProofScript |
|---|---|
| kernel | ProofScript kernel (TypeScript), Lean-compatible; proofs exported and re-checked by Lean's kernel in CI |
| elaborator, tactic framework | ProofScript elaborator and tactics (untrusted; produce kernel terms) |
| infoview (goal display) | goal panel over an LSP side-channel, in any editor; machine-readable for agents |
| `lake build` | `proofscript check` / `proofscript build`; plain `tsc` still works |
| Mathlib | an npm library ecosystem; importing Lean libraries (core, Mathlib) as kernel terms is a later phase |
| `lean4export` | `proofscript export --lean` |

## Where ProofScript deliberately differs

1. **Code is JavaScript.** Definitions run as the TypeScript they are, with JavaScript's semantics (floats, UTF-16 strings, `===`), not as Lean-compiled code. Integer and mathematical reasoning comes through proved refinements.
2. **Unverified code coexists.** Most of a TypeScript program is never reflected into the logic, and it doesn't need to be. Lean has no equivalent of the boundary with unverified code ([design §8.4](02-language-design.md#84-boundaries-with-unverified-code)).
3. **Two type checkers.** `tsc` keeps running on every file as a fast, unsound first pass. ProofScript is the sound second pass.
4. **Syntax is TypeScript's.** Tactic scripts are function calls, binders are callback parameters, and notation is limited to what TypeScript expresses. There is no user-definable notation.
