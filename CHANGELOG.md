# Changelog

ProofScript ships patch releases (0.0.x) until the 0.1.0 MVP. See [docs/v0.1.md](docs/v0.1.md).

## 0.0.1 (2026-11-04)

First tagged patch release.

- **Kernel:** a Lean 4 type theory checker in TypeScript, the only trusted component. Lean Kernel Arena: 235 passed, 0 failed, 3 declined. Accepts all 58,167 declarations of Lean's `Init`.
- **`proofscript check`:** theorems in TypeScript (tactic and term proofs), inductive types and propositions, preconditions and postconditions, `while`/`for` loops with invariants and termination measures, local mutation, read-only arrays with proved-in-bounds indexing. Lean is used as an untrusted proof engine; every proof is re-checked by the kernel. Results carry trust footprints.
- **Integer overflow (D32):** every `+`, `-`, `*` on `nat`/`int` in running code is proved to stay within ±(2⁵³ − 1). Exempt: sums of small constants and counts in recursion (bounded by recursion depth; listed as the assumption "recursion depth below 2^30"). Array lengths are below 2³² (an ECMAScript guarantee) and are available as facts.
- Side-condition guards are emitted as separate statements, so proofs about definitions see clean values; `unfold(f)` clears them.

Known limitations: overflow bounds that need nonlinear arithmetic (e.g. `n * n` under `n < 2^26`) are not proved automatically yet.
