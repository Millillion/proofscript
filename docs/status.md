# Status and Evidence

Last updated: 2026-11-03. See the [implementation plan](design/07-implementation-plan.md) for the milestones and the evidence strategy.

## Milestones

| Milestone | State |
|---|---|
| M0 Scaffolding | Done |
| M1 Kernel | Done, with performance work remaining |
| M2 Theorem elaboration | Working end to end (via Lean as an untrusted engine, D30) |
| M3 Tactics, `examples/math` | Lean's tactics are available through the engine; surface coverage in progress |
| M4 Reflection and refinements | Postconditions (generated obligations, proved automatically) and preconditions (enforced at every call in verified code) work for pure functions over `nat`/`int`/`bool`/inductive types |
| M5 Imperative verification | In progress: local `let` mutation, `while`/`for` loops with invariants (`x satisfies R;`) and termination measures (`e satisfies Decreases;`), read-only arrays with proved-in-bounds indexing, `includes`/`every`/`some`, `Math.floor(a / b)` on `nat`. Loop postconditions are proved automatically through invariants. Not yet: mutating arrays or objects. |
| M6 Heap, boundaries, apps | Not started |
| M7 Editor | Not started |

## Kernel evidence

The kernel (`packages/kernel`) is the only trusted component.

- **Lean core library:** all 58,167 declarations of Lean's `Init` accepted (5 min 42 s, 2 GB, before the performance work). `Init.Prelude`: 1,821 declarations in 1.0 s.
- **[Lean Kernel Arena](https://arena.lean-lang.org):** full run (bugs, corner cases, other, tutorial, perf): **235 passed, 0 failed, 3 declined**.
  - `bugs/`: every recorded soundness bug (found in any Lean kernel, including Lean's own) is rejected.
  - `tutorial/`: 141/141 (94 accept, 47 reject).
  - `corner-cases/`, `other/`: all pass. Two corner cases are documented as non-terminating in Lean's kernel too; they time out here as well (scored as declines).
  - `perf/`: correct on everything that completes. The heaviest `decide` stress test (`magma-list-deep-n36`, which takes Lean's C++ kernel 83 s and 8 GB) exceeds the 390 s limit. Typical decide-heavy tests run at about 1.7× the C++ kernel's time.
- **Differential mutation fuzzing against Lean's official kernel:** 500 mutants of valid exports, every one judged identically after one fix (the claimed types of quotient constants are now ignored, as Lean does). No mutant has ever been accepted by this kernel and rejected by Lean.
- **Unit tests:** substitution and abstraction laws; the universe-level decision procedure checked against brute-force evaluation on 3,000 random level pairs.

## Checker evidence

`proofscript check` (`packages/checker`) translates TypeScript to Lean, proves with Lean (untrusted), and checks the exported proofs with the kernel.

- End-to-end fixtures that must verify: `nat` arithmetic, a recursive tree type, automatically proved postconditions with preconditions, and loops (`sumOdds(n) === n * n` through a `while` loop's invariant; a `for` loop over an array with every index proved in bounds).
- Red-team fixtures that must not: a false theorem; a proof using `sorry` (reported as *admitted*, never *verified*); IEEE-754 `number` arithmetic treated as integers; `===` on objects treated as structural equality; a wrong postcondition; a loop invariant that is not preserved; an out-of-bounds array read; a loop without a decreasing measure.
- Every result carries a trust footprint: the axioms it depends on, and the TypeScript functions whose translation it trusts.

## Known gaps

- Overflow bounds that need nonlinear arithmetic (e.g. `n * n` under a bound on `n`) are not proved automatically yet.
- Shared (aliased) mutable data, classes, async: not yet in the logic. Mutation is supported without aliasing (0.0.3).
- Preconditions are enforced at calls inside verified code; calls from unverified code are not yet reported (the "boundary preconditions" audit).
- Proving requires Lean (D30); its replacement by Lean in WebAssembly is planned (D31).
- Certificate caching (checking without Lean) is not implemented yet; it needs the statement-binding check described in D30's notes.
