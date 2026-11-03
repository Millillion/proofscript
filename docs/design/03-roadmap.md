# ProofScript Roadmap

Status: **draft v0.2** (2026-11-02). Updated for the TypeScript-only surface ([04](04-surface-syntax.md)) and the decisions in the [decision log](06-decision-log.md).

## Ordering principle: kernel first

The kernel and theorem proving come first, and everything else elaborates into them ([D4](06-decision-log.md#d4-build-order-kernel-first--default)):

1. **Soundness can't be retrofitted.** If contracts were first discharged by a trusted SMT pipeline, every later feature would be built on a path that must eventually be ripped out (R15).
2. **It matches the core ambition**: theorems and proofs in TypeScript, behaving like Lean.
3. **Contracts are just theorems.** Refined parameter and return types, invariants and assertions all elaborate into kernel propositions.

Because ProofScript is plain TypeScript (D5), there is no parser, loader or editor-syntax work to do before the kernel. Projects can adopt the types package on day one, and `tsc`, Node and every other tool already work.

## Phase 0 — Scaffolding

- Monorepo: `packages/proofscript` (the types + inert runtime package users import), `packages/kernel`, `packages/checker` (front end + CLI); test runner; CI.
- `proofscript check` CLI skeleton on the TypeScript 6 compiler API: load a `tsconfig.json` project, find declarations that use ProofScript symbols (resolved by symbol, not name), report positions.
- **Superset conformance suite:** `proofscript check` on ordinary TS projects (and TypeScript's own test corpus) must report nothing and change nothing (R1, R10).

**Exit:** `proofscript check` runs on real projects; the prototype in `docs/design/typescript-only/` is its first test fixture.

## Phase 1 — Kernel and theorem proving ("Lean in TypeScript")

- **Kernel**: Lean 4's type theory in TypeScript: expressions with de Bruijn indices, universe levels, inductive families with recursors, definitional unfolding, proof irrelevance, eta, quotients. Small and separately reviewable.
- **Lean interop**: export to Lean 4's kernel export format, with CI re-checking every proof in Lean; import small Lean developments to cross-test our kernel against Lean's.
- **Elaborator, theorem side**: theorem functions (`prove(…)` statements and Curry–Howard return types), `Prop`, inductive propositions (`interface` + `declare namespace`), discriminated unions as inductive types, `nat`/`Nat`/`Int`, `eq`, `forall`/`exists`/`implies`, implicit value parameters, term proofs (recursion, `switch`/`?:` as pattern matching), structural recursion checking.
- **Core tactics**: `intro`, `exact`, `apply`, `rfl`, `cases`, `induction`, `rw`, `simp`, `omega` (producing kernel terms), `decide`, `calc`, `have`.
- `sorry`, axioms, and **trust footprints / `proofscript audit`** from day one.
- **Prelude**: `Nat`, `Int`, `Bool`, lists, and their basic lemmas.

**Exit:** a library of nontrivial theorems (list lemmas, arithmetic, insertion sort's correctness) written in TypeScript, checked by our kernel *and* re-checked by Lean.

## Phase 2 — Reflecting pure TypeScript and refinements

- Interpretation of TS types: discriminated unions, readonly records, tuples, arrays and literal types.
- Kernel models: IEEE-754 `Float64` with ECMAScript's operations; `int`/`nat` and the theorem that safe-integer arithmetic is exact; UTF-16 strings; `bigint`.
- **Reflection** of pure, total TS functions (including local `let` mutation and loops), and of built-ins such as `Array.prototype.every`.
- Refinements `T & R`, `Is<typeof pred, Args>`, preconditions and postconditions, value indices (`n extends nat`, `typeof x`), `satisfies` assertions.
- **Editor**: language-server goal panel and diagnostics (as a TS server plugin plus a ProofScript language server).

**Exit:** the `List`, `Vec` and `binarySearch` examples verify end to end in VS Code, and the two bad calls in the prototype's `main.ts` are rejected.

## Phase 3 — Imperative code and automation

- Weakest-precondition verification for local-imperative code: loops with `satisfies` invariants, early return, exceptions; invariant inference for simple loops.
- SMT oracle (Z3/cvc5 in wasm) with proof reconstruction; uncertified results tracked as `smt` ([D3](06-decision-log.md#d3-trust-of-automation-smt-decision-procedures--default)).
- Heap model and frames (`Reads`, `Modifies`, `Old`); mutable arrays, `Map`, `Set`.
- Validators for data from unverified code.
- **Deep-embedded semantics of the verifiable JavaScript subset**, an interpreter tested against test262 and the major engines, and the adequacy theorem that takes reflection out of the trusted base.
- Assurance levels 0–4 enforced from `tsconfig.json`.

**Exit:** a real npm library (e.g. `base64-js`, the March prototype's target) verified at level 3 and published with its specs, consumed unchanged by plain TS projects.

## Phase 4 — Ecosystem

- `async`/`await`, callbacks, classes.
- Tactics written in ProofScript.
- Lean library import (core, potentially Mathlib).
- Community specs for popular packages, clearly marked as assumptions.
- Performance: incremental checking, caching, an optional Rust/wasm kernel.
- Optional: the dedicated-syntax sugar of [02 §7](02-language-design.md#7-concrete-syntax), if real use shows it is needed.
- Long term: verify the ProofScript kernel in ProofScript.

## Immediate next steps

1. Jordan reviews the [decision log](06-decision-log.md) at leisure. Defaults stand until changed.
2. Write the kernel specification (term language, typing rules, inductive declarations, reduction) as a design note.
3. Begin phase 0 and the kernel.
