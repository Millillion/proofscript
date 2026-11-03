# @proofscript/kernel

The trusted core of ProofScript: a type checker for Lean 4's type theory, written in TypeScript.

Every theorem ProofScript accepts is a term this kernel has checked. Everything else in ProofScript (the TypeScript front end, elaborator, tactics, decision procedures, SMT solvers) is untrusted: it produces terms, and this package decides whether they are proofs.

## What it checks

The type theory is Lean 4's ([Carneiro, *The Type Theory of Lean*](https://github.com/digama0/lean-type-theory/releases)):

- dependent functions, `let`, a non-cumulative universe hierarchy with level parameters, `max` and `imax`;
- an impredicative, definitionally proof-irrelevant `Prop`;
- mutual and nested inductive families with generated recursors, eta for structures, K-like reduction;
- quotient types;
- definitional unfolding with reducibility hints, `Nat` literals with GMP-style arithmetic (as `bigint`), `String` literals.

## Input

Declarations come from [lean4export](https://github.com/leanprover/lean4export)'s NDJSON format, so the kernel can check anything Lean itself produces, and runs the [Lean Kernel Arena](https://arena.lean-lang.org) benchmark unmodified:

```bash
node --stack-size=65500 src/cli.ts file.ndjson   # exit 0 accept, 1 reject, 2 decline
node scripts/arena.ts <lean-kernel-arena checkout> [filters...]
```

ProofScript's own elaborator will produce declarations in the same form.

## What is derived, not trusted

Data an export supplies that the kernel can derive is re-derived and compared:

- inductive metadata (`isRec`, `isReflexive`, `numNested`, …);
- recursor types and computation rules;
- the quotient constants.

A forged recursor or quotient is a rejection, not a new axiom.

## Deliberate differences from Lean's C++ kernel

- **Universe level comparison is complete.** Lean's `is_geq` is a sound but incomplete heuristic. This kernel decides `l₁ ≥ l₂` exactly, by case-splitting on parameters that occur under `imax` (`src/level.ts`).
- **No native evaluation.** `Lean.reduceBool` and `Lean.reduceNat` (used by `native_decide`) are declined, never trusted.

## Files

| File | Contents |
|---|---|
| `name.ts` | interned hierarchical names |
| `level.ts` | universe levels and the decision procedure for `≥` |
| `expr.ts` | locally nameless expressions, substitution, abstraction |
| `env.ts` | declarations, environments |
| `typechecker.ts` | inference, weak-head normalization, definitional equality |
| `inductive.ts` | inductive declarations, positivity, recursors, nested inductives |
| `check.ts` | adding declarations; quotients |
| `ndjson.ts` | lean4export reader |
| `cli.ts` | arena-compatible command line |

## Provenance

The algorithms follow Lean 4's C++ kernel (`src/kernel/`), which is Copyright Microsoft Corporation and released under the Apache License 2.0, as the de facto specification of the theory's decidable fragment. The code in this package is an independent TypeScript implementation; no Lean source code is copied. "Lean" is a trademark of the Lean FRO; this project is not affiliated with or endorsed by it.
