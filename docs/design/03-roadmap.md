# ProofScript Roadmap

Status: **draft v0.1** (2026-11-02). Implements [02-language-design.md](02-language-design.md).

## Ordering principle: kernel first

[research/04](../research/04-syntax-and-tooling.md) proposes starting with a Dafny-style contract checker backed by Z3, then adding the kernel. This roadmap reverses that: **the kernel and the ghost layer come first, and everything else elaborates into them.**

Reasons:

1. **Soundness can't be retrofitted.** If contracts are first discharged by a trusted SMT pipeline, every later feature is built on a path that must eventually be ripped out (R15). Building the kernel first means every feature is sound the day it ships.
2. **It matches the core ambition**: writing theorems and proofs in TypeScript. A working "Lean in TypeScript syntax" is the most distinctive and most demonstrable milestone.
3. **Contracts are just theorems.** `requires`/`ensures`, loop invariants and refinement types all elaborate into kernel propositions. With the kernel in place they are a front-end feature, not a second verifier.

The syntactic strip pass still comes first (phase 0), because it is cheap and is what makes `.pts` files usable everywhere from day one (R1, R3).

## Phase 0 — Foundations and spike

- Repository scaffolding: TypeScript monorepo, test runner, CI.
- **`strip`**: whitespace-preserving eraser for the §7 grammar, built on a fork of the TypeScript 6 scanner/parser.
- **Superset conformance suite (R1, R2)**: run `strip` over TypeScript's own test corpus and real-world projects; it must be the identity on every valid `.ts` file. This suite is permanent CI.
- `node --import proofscript/register` loader; esbuild/Vite plugin.
- **Spike to confirm TypeScript 7.1 content mappers** work for `.pts` (generated TS, mappings, extra diagnostics in `tsc` output), with Volar on TS 6 as the fallback. The research claims rest on the 7.1 beta and on source reading, so they need confirming.
- TextMate grammar for syntax highlighting.

**Exit:** `.pts` files with ProofScript syntax type-check with `tsc`, run under Node and bundle with Vite. Nothing is verified yet.

## Phase 1 — Kernel and theorem proving ("Lean in TypeScript")

- **Kernel**: LeanTT in TypeScript: expressions with de Bruijn indices, universe levels, inductive families with recursors, definitional unfolding, proof irrelevance, eta, quotients. Kept small and separately reviewable.
- **Lean export/import**: emit Lean 4 kernel export format; CI re-checks all proofs with Lean's kernel. Also import small Lean developments, to cross-test our kernel against Lean's.
- **Elaborator for the ghost layer**: `theorem`, `inductive`, `ghost function`, `Prop`, `Nat`/`Int`, `eq`, `forall`/`exists`, `==>`; implicit arguments via unification; term proofs with `switch`-as-pattern-matching; structural recursion checking.
- **Core tactics**: `intro`, `exact`, `apply`, `rfl`, `cases`, `induction`, `rw`, `simp` (basic), `omega` (Presburger arithmetic producing kernel terms), `decide`, `calc`.
- `admit`, `axiom`, and **trust footprints / `proofscript audit`** from day one.
- A prelude: `Nat`, `Int`, `Bool`, `List`, equality and arithmetic lemmas.

**Exit:** a library of nontrivial theorems (list lemmas, arithmetic, a sortedness proof of insertion sort written as a ghost function) checked by our kernel *and* re-checked by Lean.

## Phase 2 — Reflecting pure TypeScript

- Interpretation of TS types (§4.1): discriminated unions → inductives, readonly records/tuples/arrays, literal types.
- Kernel models: `Float64` (IEEE-754 binary64 with ES operations), `int`/`nat` refinements and the prelude theorem that safe-integer arithmetic is exact, `JSString`, `bigint` → `Int`.
- **Reflection** (§6.2) of pure, total TS functions, including local `let` mutation and loops via state-passing.
- Contracts on pure functions: `requires`, `ensures`, `decreases`; refinement types `(x: T) where P`; value-indexed types `<n: nat>`.
- Declaration view + TS integration (content mapper / Volar), `.d.pts` generation, cross-module specs.
- **Editor**: LSP side-channel with goal panel; diagnostics positioned in `.pts` source.

**Exit:** the `List` / `binarySearch`-over-immutable-data examples from the design verify end to end inside VS Code, and `tsc` reports proof failures.

## Phase 3 — Imperative code and automation

- WP-based VC generation for local-imperative code (loops, early return, exceptions); invariant inference for simple loops.
- SMT oracle (Z3/cvc5 in wasm) with proof reconstruction for linear arithmetic and uninterpreted functions; uncertified results tracked as `smt`.
- Heap model and dynamic frames (`reads`, `modifies`, `old`), mutable arrays, `Map`/`Set`.
- Validators: generation from types, verified copy-in.
- **Deep-embedded semantics of the verifiable JS subset S**, an extracted interpreter differentially tested against test262 and V8/SpiderMonkey/JSC; adequacy theorem for reflection, which moves reflection out of the TCB.
- Assurance levels 0–4 enforced from `tsconfig`.

**Exit:** a real npm library (e.g. `base64-js`, which is also the original target from the March prototype) verified at level 3, published with `.d.pts` specs, and consumed unchanged by plain TS projects.

## Phase 4 — Ecosystem

- `async`/`await` and callbacks; classes and prototypes in S.
- Tactic metaprogramming in ProofScript itself.
- Lean library import (core, and potentially Mathlib).
- Community `.d.pts` repository for popular packages (the DefinitelyTyped analogue), clearly marked as assumptions.
- Performance: incremental checking, caching of kernel results, optional Rust/wasm kernel if profiling demands.
- Long term: verify the ProofScript kernel and strip pass in ProofScript.

## Immediate next steps

1. Decide the open questions in [design §12](02-language-design.md#12-open-design-questions) that block phase 0–1 (kernel strategy, file extension).
2. Write the formal grammar addendum (the precise §7 productions and their disambiguation rules) and the kernel specification (term language, typing rules, inductive declarations), both as design notes.
3. Begin phase 0.
