# Changelog

ProofScript ships patch releases (0.0.x) until the 0.1.0 MVP. See [docs/v0.1.md](docs/v0.1.md).

## 0.0.9 (2026-11-07)

- **Certificates establish termination.** Every recursive function (including every loop) now also has a uniqueness theorem: any function satisfying its equation equals it. Lean proves it along the function's own recursion when the certificate is made, and ProofScript binds it like every other statement. Results checked from certificates no longer list "terminates (proved by Lean when the certificate was made)", unless Lean could not prove one. All examples and fixtures are covered.
- **Elaborator:** dependent arrow types (`(x : A) → B`, with implicit binders and tactic defaults) and `∀ {T : Type} …` binders.
- **Decision log D34–D40**, and a [review queue](docs/review-queue.md) of the decisions that need Jordan's review before 0.1.0.

## 0.0.8 (2026-11-07)

- **`examples/base64`:** a verified drop-in replacement for base64-js 1.5.1 (`byteLength`, `toByteArray`, `fromByteArray`).
  - **Proved:**
    - every access is in bounds and every write lands in the output buffer;
    - no arithmetic overflows;
    - encoded units are alphabet characters and decoded values are bytes;
    - every sextet survives the alphabet (`decode_encode_unit`);
    - the sextets of any group of three, two or one bytes decode back to those bytes;
    - the encoder never emits `=`.

    In total, 18 theorems.
  - **Not yet one theorem:** the whole-array round trip `toByteArray(fromByteArray(x)) = x`, which composes these facts.
  - **Tested:** base64-js's own test suite passes unmodified, 57/57, including its 64 MB round trip. A differential test against base64-js covers 27,000 random inputs, with identical results and errors.
- **Language:**
  - `%` on `nat`.
  - Masks `x & (2^k − 1)`, exact for any safe integer, as in JavaScript.
  - Shifts `>>`, `>>>` and `<<` by constants, with their range obligations.
  - `String.fromCharCode`.
  - Strings carry the ECMAScript length bound (at most 2⁵³ − 1) where loops need it.
- **Automation (modular reasoning):**
  - After `const x = f(…)`, `f`'s proved postconditions are facts about `x`.
  - Callees with postconditions are reasoned about through them, not unfolded, and their lemmas are given to `grind`.
  - A predicate whose body is one expression is stated by its body (`i % 3 === 0`, not `multipleOf3 i = true`), so `omega` sees it directly.
  - Side conditions copy hypotheses that `let` values depend on, so `simp` can still use them.
  - Guards of `if` conditions are proved before the `if`.
  - Loop invariant tactics see what the loop body uses.
- **Fixes:**
  - a reserved word with a suffix produced invalid Lean (`«end»_7`);
  - loops inside functions with `Modifies` crashed;
  - `Le<typeof s.length>` on strings;
  - side-condition counts leaked between functions;
  - a non-recursive function was listed as needing termination in certificate results.
- **Lean Kernel Arena subset in the tests:** 179 arena tests (all recorded soundness bugs, the tutorial, the decidable corner cases, Init.Prelude) are packed in `packages/kernel/test/arena` and run without Lean in about a second.
- **npm package build:** `node scripts/build-npm.ts` builds the `proofscript` package as JavaScript, with the checker, the kernel and the `proofscript` command. Installed from its tarball into a fresh project, `npx proofscript check --certificate` verifies the tutorial. Publishing waits for 0.1.0.
- **CI:**
  - Without Lean: all tests, the arena subset, every example from its certificate, and the npm package in a fresh project.
  - With Lean (elan installed in CI): everything proved from scratch.
  - CI had been failing since 0.0.6 on a test that needed Lean.
- 65/65 tests pass.

## 0.0.7 (2026-11-06)

- **`proofscript audit`:** what a project's results rest on. It collects, over the whole project, each axiom, trusted translation and assumption, with the theorems that depend on it. It also reports the **boundary** (exported functions with preconditions, and calls from unverified code that nothing proves) and the trusted base. `--json` prints it for tools; it works with Lean or from a certificate.
- **Callers are checked:** a function without a spec of its own that calls a function with preconditions is now verified code, so the preconditions are proved at the call. If it cannot be translated (for example, it uses `number`), the call is reported as unverified rather than trusted silently. The audit found such a call in `examples/math` (`third()` calling `get`), which is now proved.
- **`Nat` and `Int` (bigint) arithmetic is exact:** no 2⁵³ overflow checks, as in JavaScript. Bigint literals take their type from context (`n === 0n` on a `Nat` is `Nat`), instead of always `Int`.
- **Docs:** a [tutorial](docs/tutorial.md), whose code is a checked project ([`examples/tutorial`](examples/tutorial), 12 theorems, with a certificate), and a [reference](docs/reference.md) for every ProofScript type, function, tactic and supported TypeScript construct. The README describes the working system.
- Termination assumptions from certificates are listed per function.
- Fixtures: `bad-caller`, `boundary`. Tests: `audit.test.ts`, tutorial tests. 57/57 tests pass.

## 0.0.6 (2026-11-05)

- **Proof certificates: checking without Lean.** `proofscript check --write-certificate` proves with Lean and saves `proofscript.cert` (the kernel export of every checked declaration, gzipped). `proofscript check --certificate` checks the project against it with only Node: every declaration is re-checked by ProofScript's kernel, and every theorem, definition and type is *bound* to the current TypeScript. A theorem verifies only if it is bound; anything not covered (an edited statement, a new theorem) is reported as needing Lean, never as verified.
- **Binding** ([docs/certificates.md](docs/certificates.md)): ProofScript now elaborates the generated statements itself (a parser for the generated Lean subset and a small elaborator with unification and instance resolution), and the kernel decides whether the certificate's declarations have exactly those types. Definitions are bound by their equations (`f params = body`, which Lean proves when the certificate is made), inductive types by their constructors. Library constants a statement depends on must match content hashes of the pinned toolchain's library (`library.json`, generated by `scripts/library.ts`). Every statement, signature and constructor in the repository (151 declarations) binds.
- **Red-team tests:** forged certificates made with Lean itself (a weakened theorem, a redefined function with a consistent equation, an inductive type with an extra constructor, `sorry`), a corrupted proof, a redefined `Nat.add`, a certificate from another toolchain, and edited TypeScript (changed statement, changed definition, new theorem). None verifies.
- `examples/math` ships its certificate: its 28 theorems verify without Lean in about 8 seconds.
- **Setup:** Lean's tools are found in `~/.elan/bin` even when it is not on `PATH`; lean4export is built at a pinned commit; without Lean, `proofscript check` explains how to install it (or to use a certificate). A `proofscript` command (`packages/checker/bin/proofscript.mjs`) runs the checker with the stack it needs.
- Trust footprints of certificate checks list the recursive functions whose termination Lean proved when the certificate was made (a certificate cannot show termination by itself).
- Tests run one file at a time with a 2 GB heap. 50/50 tests pass.

## 0.0.5 (2026-11-04)

- **`examples/math`:** a mathematics library written in TypeScript, 28 theorems, all checked by the kernel:
  - arithmetic (commutativity, associativity, distributivity, `(a + b)² = a² + 2ab + b²`);
  - an inductive family of propositions (`Even<n>`) with proofs by induction;
  - lists: `append` is associative, `reverse` is an involution and distributes over `append`, lengths add up;
  - insertion sort: the result is sorted, contains the same elements with the same multiplicities, and has the same length;
  - value-indexed vectors (`Vec`, `Fin`, `replicate`, `zip`, `get`).
- **Tactics:** `split`, `simp_only(…)`, `andThen(t₁, t₂, …)` (Lean's `<;>`), `attempt(t)` (Lean's `try`, a reserved word in JavaScript), `first(…)`, `grind(lemmas…)`.
- Arithmetic on conditional expressions (`(x === y ? 1 : 0) + n`).
- 37/37 tests pass.

## 0.0.4 (2026-11-04)

- **Value-indexed (dependent) types:** refinement aliases such as `type Vec<T, n extends nat> = readonly T[] & Length<n>` and `type Fin<n extends nat> = nat & Lt<n>` work as parameter types (preconditions), return types (postconditions), invariants and theorem hypotheses. New `Length<n>` refinement for arrays and strings.
- **Value parameters:** `n extends nat` is determined by a `Length<n>` refinement of a parameter (`zip<A, B, n>(xs: Vec<A, n>, ys: Vec<B, n>)`: `n` is `xs.length`, and `ys` must match). Callers never pass it.
- **`typeof x` in types** means the value of `x`: `replicate(n, x): Vec<T, typeof n>`.
- **Tuples:** `[A, B]` types and literals.
- **Modular verification:** callers' checks use their callees' proved postconditions.
- Functions with only preconditions (refined parameters) are verified code too. Theorem parameters keep their refinements as hypotheses.
- Fixes: postconditions through a shared alias no longer overwrite each other; value parameters are found alongside ordinary type parameters; refinements and value parameters are carried into loops under the loop's own names.
- The design prototype (`docs/design/typescript-only/`) now verifies end to end (9/9), including `Vec`, `zip`, `replicate` and `get`. Its binary search awaits signed indices.
- Fixtures: `good-indexed`, `bad-indexed`. 36/36 tests pass.

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
