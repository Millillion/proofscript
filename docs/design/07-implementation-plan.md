# Implementation Plan and Evidence Strategy

Status: **v0.1** (2026-11-03). Implements the [roadmap](03-roadmap.md) under the [decision log](06-decision-log.md).

The goal is not only to build ProofScript but to produce **evidence, strong enough to convince a skeptic, that it is correct**. "Correct" has two halves, and each has its own evidence:

- **Sound:** ProofScript never accepts something false.
- **Complete enough:** it accepts the true things people actually write.

## 1. Components

| Package | Contents | Trusted? |
|---|---|---|
| `packages/kernel` | Lean 4 type theory checker: levels, expressions, environment, inductive types and recursors, quotients, definitional equality, Nat/String literal extensions; lean4export (NDJSON) reader and writer | **Yes**: the only trusted code |
| `packages/proofscript` | The package users import: types (`nat`, `Lt`, `Is`, `Proof`, …) and inert theorem/tactic functions | No (has no semantics of its own) |
| `packages/checker` | Front end on the TypeScript compiler API, the surface table, elaborator (TS → kernel terms), reflection, tactics, decision procedures, VC generation, the `proofscript` CLI (`check`, `audit`, `export`) | No |
| `examples/*` | Example libraries and apps (§4) | — |

Everything is TypeScript on Node 24, with no runtime dependencies besides `typescript` in the checker. Tests use Node's built-in runner (`node --test`) and its coverage.

## 2. Evidence for the kernel (the part that must be right)

1. **Lean Kernel Arena.** The Lean FRO's official benchmark for alternative Lean kernels (<https://arena.lean-lang.org>). Our kernel reads the same lean4export NDJSON input and answers accept/reject by exit code, so it runs the arena unmodified. It covers:
   - `tutorial/`: one test per feature of the type theory, in implementation order. This drives development.
   - `bugs/`: every soundness bug found so far in *any* Lean kernel, including the official one. All must be rejected.
   - `corner-cases/` and `other/`: targeted accept/reject tests.
   - Real-world corpora: Lean's `Init`, `Std`, and eventually Mathlib. All must be accepted.

   **Target:** a perfect record on everything except Mathlib in phase 1; Mathlib when performance allows. We will submit the kernel to the arena as a public checker.
2. **Differential testing against Lean.** Every proof ProofScript produces is exported and re-checked by Lean's own kernel in CI. Any disagreement fails the build.
3. **Mutation fuzzing.** Take accepted declarations (from Init/Std and our own output), apply random mutations (swap subterms, bump universe levels, perturb de Bruijn indices, alter recursor rules), and check our kernel against Lean's kernel on each mutant. The two must agree on every accept and reject. This finds soundness gaps that hand-written tests miss.
4. **Unit and property tests** for the internals: level normalization and `≤`; instantiate and abstract; weak-head normalization; and properties such as `infer(t) ≡ infer(whnf(t))`, and definitional equality being reflexive and symmetric on random well-typed terms.
5. **Mutation testing of the kernel code itself.** Deliberately weaken checks in the kernel source (delete a universe check, skip a positivity check) and confirm the test suite catches each one. A check that can be removed without any test failing is untested.
6. **Coverage:** 100% branch coverage of the kernel, enforced in CI.
7. **Small and reviewable:** the kernel stays self-contained, with no dependency on the checker, so it can be audited in isolation.

## 3. Evidence for everything above the kernel

Nothing above the kernel is trusted: a bug there can make ProofScript reject true things or report confusing errors, but it can't make a false theorem check, because the kernel re-checks everything. Two things are exceptions, and get the most scrutiny:

- **reflection** (how a TS function becomes a kernel definition);
- **the JavaScript model** (what `number`, `===` and `Array.prototype.every` mean in the logic).

These are trusted until phase 3's adequacy proofs.

1. **Soundness red-team suite.** One fixture per known way to fool a verifier, each of which must be **rejected**:
   - TypeScript loopholes: `any`, `as`, bivariance, non-null `!`, unchecked indexing, lying `.d.ts` files;
   - non-terminating functions used in specs;
   - mutation through aliases, getters, `Proxy`;
   - JavaScript traps: `NaN`, `-0`, overflow past 2⁵³, `0.1 + 0.2`, sparse arrays, string length versus code points, exceptions;
   - attempts to derive `False` from `sorry`-free code.

   The suite grows with every bug found.
2. **Runtime cross-checking of specs.** Specs in ProofScript are executable TypeScript predicates, so every verified function in the test corpus and examples is also run on random inputs, with the spec checked at runtime. A verified function whose runtime behaviour ever violates its spec means the JavaScript model or reflection is wrong. Theorems are likewise run as property tests. This gives continuous, automatic evidence for the two trusted pieces above.
3. **JavaScript model differential tests.** The kernel's models of IEEE-754 arithmetic, `Math.floor`, UTF-16 strings, `===`/`Object.is` and so on are evaluated and compared against V8 on large random inputs (including NaN, ±0, ±∞, subnormals and lone surrogates). Later, a filtered subset of test262.
4. **Golden diagnostics tests.** Fixture files paired with the exact diagnostics expected: verified, or a specific error at a specific position.
5. **Superset conformance.** `proofscript check` on ordinary TypeScript (TypeScript's own test corpus and real open-source projects) must report nothing and never crash (R1, R10).
6. **Elaborator round trips.** For each surface construct, elaborate, export to Lean, pretty-print, and check that Lean agrees with the intended statement.

## 4. Example libraries and apps

Each one must:
- type-check with `tsc`, run, and pass its own tests;
- pass `proofscript check`;
- pass Lean re-checking;
- report a clean `proofscript audit`.

| Example | Demonstrates | Phase |
|---|---|---|
| `examples/math` | Lean-style theorem proving in TypeScript: Nat and List lemmas, inductive propositions, induction, `simp`/`omega`, insertion sort correctness | 1 |
| `examples/collections` | Verified pure data structures: List/Vec operations, a binary heap or persistent map, refinements and value indices | 2 |
| `examples/search-sort` | Verified algorithms over arrays: binary search, merge sort with permutation proof, loops with invariants | 2–3 |
| `examples/base64` | A drop-in replacement for the `base64-js` npm package, verified (round trip `decode(encode(x)) = x`, length formulas), passing the original package's test suite | 3 |
| `examples/adoption-app` | An existing-style TypeScript app (HTTP handlers, config, JSON input) adopting ProofScript incrementally: one verified module, validators at the boundary, the rest untouched TS | 3 |

## 5. Milestones

Each milestone ends with a commit, a push and a short report.

- **M0 Scaffolding:** monorepo, packages, CI, `proofscript check` skeleton.
- **M1 Kernel:** arena tutorial tests passing, one feature at a time; then `bugs/`, `corner-cases/`, `other/`; then Init and Std. Mutation fuzzing and Lean differential testing wired into CI.
- **M2 Theorem elaboration:** theorem functions, inductive propositions, discriminated unions, term proofs, export plus Lean re-check, `audit`.
- **M3 Tactics:** `intro`, `exact`, `apply`, `rfl`, `cases`, `induction`, `rw`, `simp`, `omega`, `decide`, `calc`, `have`. `examples/math` complete. **Syntax review checkpoint with Jordan.**
- **M4 Reflection and refinements:** JavaScript models, reflection of pure functions, refinements, pre/postconditions, value indices, `satisfies` assertions. Red-team and runtime cross-checking suites. `examples/collections`.
- **M5 Imperative verification:** WP for loops and local mutation, invariants, termination, SMT with reconstruction. `examples/search-sort`.
- **M6 Heap, boundaries, applications:** frames, validators, assurance levels. `examples/base64`, `examples/adoption-app`.
- **M7 Editor:** language server, goal panel.

## 6. Gates

- **No public release** before Jordan's syntax review (after M3).
- **No milestone is "done"** while any red-team, arena or differential test fails.
