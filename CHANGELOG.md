# Changelog

ProofScript ships patch releases (0.0.x) until the 0.1.0 MVP. See [docs/v0.1.md](docs/v0.1.md).

## 0.0.3 (2026-11-04)

- **Mutation (D21):** arrays and plain objects can be changed in verified code: `a[i] = v` (index proved in bounds; JavaScript would otherwise grow the array with holes), `a.push(v)` (new length proved below 2³², where JavaScript throws), `p.f = v` on objects with mutable fields, and local arrays built from literals.
- **Frames:** `Modifies<typeof a>` in a return type declares which arguments a function may change; changing any other parameter is an error. Postconditions see the new value as `typeof a` and the value on entry as `Old<typeof a>`. New `Holds<typeof pred, […]>` states relational postconditions (e.g. for `void` functions). Works through loops.
- **Translation:** a modifying function returns its result together with the new values of its modified arguments; calls are statements that rebind the caller's variables (as Aeneas does for Rust).
- **No aliasing (enforced):** no copying array/object references (`const b = a`), no returning an array parameter, no passing the same array twice to a function that modifies one of them. Exported modifying functions list the assumption "callers do not alias modified arguments".
- Definitions are checked (and kernel-checked) even when a project has no theorems. Non-recursive predicates are simp lemmas, so callers' preconditions can use them. "Array length < 2³²" facts are attached only where overflow checks need them.
- Fixtures: `good-mutation`, `bad-alias`, `bad-undeclared-modify`, `bad-old`, `bad-write-oob`. 34/34 tests pass.

## 0.0.2 (2026-11-04)

- **Structures:** plain object types (`type Point = { readonly x: nat; readonly y: nat }`) and interfaces are data types in the logic: field access, object literals (including shorthand properties), structural equality with `eq`.
- **Strings with JavaScript's semantics:** a string is its sequence of UTF-16 code units, so `"😀".length === 2` is a theorem and lone surrogates are representable. Supported: literals, `===`, `+` (concatenation of two strings), `.length`, `startsWith`, `endsWith`, `charCodeAt` (index proved in bounds). Mixing strings with other values in `+` is rejected (JavaScript would coerce).
- **Partial failures:** a failing declaration no longer blocks the rest. ProofScript removes it and everything depending on it, rebuilds, and verifies the remainder.
- Fixtures: `good-struct`, `good-string`, `bad-string`, `bad-struct`, `mixed`. 29/29 tests pass.

## 0.0.1 (2026-11-04)

First tagged patch release.

- **Kernel:** a Lean 4 type theory checker in TypeScript, the only trusted component. Lean Kernel Arena: 235 passed, 0 failed, 3 declined. Accepts all 58,167 declarations of Lean's `Init`.
- **`proofscript check`:** theorems in TypeScript (tactic and term proofs), inductive types and propositions, preconditions and postconditions, `while`/`for` loops with invariants and termination measures, local mutation, read-only arrays with proved-in-bounds indexing. Lean is used as an untrusted proof engine; every proof is re-checked by the kernel. Results carry trust footprints.
- **Integer overflow (D32):** every `+`, `-`, `*` on `nat`/`int` in running code is proved to stay within ±(2⁵³ − 1). Exempt: sums of small constants and counts in recursion (bounded by recursion depth; listed as the assumption "recursion depth below 2^30"). Array lengths are below 2³² (an ECMAScript guarantee) and are available as facts.
- Side-condition guards are emitted as separate statements, so proofs about definitions see clean values; `unfold(f)` clears them.

Known limitations: overflow bounds that need nonlinear arithmetic (e.g. `n * n` under `n < 2^26`) are not proved automatically yet.
