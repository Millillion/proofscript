# Decision Log

Status: living document. Started 2026-11-02.

Every design decision made so far, with the alternatives that were considered. **Status** is one of:

- **Decided**: chosen by Jordan.
- **Default**: chosen by Claude as the recommendation, adopted so implementation can start, **pending Jordan's review**. Anything marked Default can be reopened.

When a decision changes, update its entry and note the date rather than deleting history.

---

## Foundations

### D1. Kernel — **Decided** (2026-11-02)
- **Chosen:** our own kernel for Lean 4's type theory, written in TypeScript, with every proof exported to Lean's kernel export format and re-checked by Lean (and other independent checkers) in CI.
- **Alternatives:**
  - *Lean 4 as the checker from day one* (translate to Lean, run Lean). Faster start and a battle-tested kernel, but a heavy native dependency, a slower editor loop, no in-browser checking, and ProofScript's correctness bound to a translation into a different surface language.
  - *A different logic* (refinement types + SMT only, like Liquid Haskell; or a custom type theory). Rejected: weaker, or no existing independent checkers and metatheory.

### D2. Logic — **Default**
- **Chosen:** exactly Lean 4's type theory (dependent functions, universes, inductive families, impredicative proof-irrelevant `Prop`, quotients, `propext`), with classical choice allowed only in erased positions.
- **Alternatives:** predicative Martin-Löf type theory (no impredicative `Prop`); an extensional type theory; adding SProp. All lose Lean compatibility.

### D3. Trust of automation (SMT, decision procedures) — **Default**
- **Chosen:** all automation is untrusted and must produce kernel-checkable proofs. Where reconstruction doesn't exist yet, an SMT result may be accepted but is recorded in the trust footprint as `smt` (forbidden at assurance level 3+).
- **Alternatives:**
  - *Trust SMT* (Dafny, Verus): fast to build, but a permanent soundness hole that is hard to remove later.
  - *No SMT at all*: purely kernel tactics, slower to reach good automation.

### D4. Build order: kernel first — **Default**
- **Chosen:** kernel and theorem proving first; contracts on ordinary code are built on top.
- **Alternative:** Dafny-style contract checker with trusted Z3 first, kernel later (research/04's proposal). Faster first demo, but every feature is built on a path that must be replaced.

## Surface

### D5. Surface syntax — **Decided** (2026-11-02)
- **Chosen:** the entire ProofScript type system is expressed in actual TypeScript (types, `satisfies`, ordinary functions). No new syntax. No comments carrying meaning.
- **Alternatives:**
  - *Dedicated grammar in `.pts` files* ([02 §7](02-language-design.md#7-concrete-syntax)): concise (`requires`, `ensures`, `theorem … by { }`, `Vec<T, n + 1>`), but needs a parser fork, a loader, TS 7.1 content mappers or Volar, and support from every tool (Prettier, ESLint, bundlers, …). Kept as possible future sugar.
  - *`//@` comment annotations in `.ts`* ([04 v0.1](04-surface-syntax.md)): zero tooling cost, but specs invisible to `tsc`. Rejected by Jordan.
  - *JSDoc tags*: collide with JSDoc's existing `@requires` and `@throws`.

### D6. File extensions — **Default**
- **Chosen:** ordinary `.ts`/`.tsx`/`.mts`/`.cts` everywhere; `*.proof.ts` is an optional convention for proof-only modules.
- **Alternatives:**
  - `.pts`/`.ptsx`/`.mpts`/`.cpts`: only needed with a dedicated grammar.
  - `.ps`: see [D7](#d7-ps-as-an-extension--default).
  - `.ps.ts`: possible as an optional naming convention for "this module contains proofs". It costs nothing, since tools see `.ts`, but it adds no meaning the checker needs.

### D7. `.ps` as an extension — **Default** (not used)
- **Chosen:** don't use `.ps`.
- **Reasons:**
  1. Under D5, ProofScript files *are* TypeScript. Any extension other than `.ts`-family breaks `tsc`, Node's type stripping (`.ts`/`.mts`/`.cts` only), Deno, Bun, Vite, esbuild, editors and linters, which would throw away the main benefit of D5.
  2. `.ps` is PostScript: registered as such in GitHub Linguist, in the `application/postscript` MIME type, and in OS file associations (macOS and Linux document viewers open `.ps` files).
  3. `.ps1` is PowerShell, and `ps` is the Unix process command, so the name is crowded for search.
- **Alternative:** `.ps.ts` as an optional convention (see D6), which keeps every tool working.

### D8. Refinements — **Default**
- **Chosen:** intersections `T & R`, where each ProofScript refinement type `R` is `unknown` to `tsc` (so `tsc` sees `T`).
- **Alternatives:**
  - *Branded types* (`T & { readonly __brand: … }`): `tsc` would force values through type guards or `as` casts, giving TS a stronger simple meaning, but adding cast noise everywhere ProofScript already proves the fact.
  - *A wrapper alias `Refine<T, P>`*: equivalent, but less compositional than `&`.
  - *Both* (brands opt-in per type): possible later.

### D9. Predicates in specs — **Default**
- **Chosen:** built-in refinements (`Lt`, `Le`, `Gt`, `Ge`, `Length`) plus `Is<typeof pred, Args>` for any ordinary TS predicate function.
- **Alternatives:**
  - *String-encoded expressions* (`Where<"x > 0">`): inline, but `tsc` can't check them and rename doesn't reach them.
  - *Fully type-level propositions* (`And<Lt<…>, Eq<…>>`): no runtime functions at all, but unreadable for anything nontrivial.

### D10. Postconditions — **Default**
- **Chosen:** explicit `int & Is<typeof post, [typeof a, typeof key]>`, so `tsc` checks the predicate's argument list.
- **Alternatives:**
  - *Implicit `Ensures<typeof post>`*: the predicate receives the function's parameters automatically. Shorter; `tsc` can't check the arguments, ProofScript does.
  - *Separate spec declarations* (e.g. a `contract(binarySearch, {...})` in a proof module): keeps signatures clean, but separates the spec from the code.

### D11. Ghost statements (assertions, loop invariants, termination measures) — **Default**
- **Chosen:** `e satisfies R;` statements. They erase to bare expression statements with no effect.
- **Alternatives:**
  - *No-op calls* `invariant(() => …)` from a `proofscript` runtime: most readable, but a runtime dependency and a closure per iteration unless a bundler strips them.
  - *Local `type` aliases* (`type _ = Invariant<…>`): rejected, because `noUnusedLocals` reports them.
  - *`satisfies` on the loop condition* (`while ((lo < hi) satisfies Inv<…>)`): attaches to the loop, but obscure.
  - *Invariant inference only*, rewriting hard loops as recursive helpers: least syntax, but forces code changes.

### D12. Theorem statements — **Default**
- **Chosen:** `prove(booleanStatement, proof)` for statements that are ordinary expressions (also runnable as property tests), and the Curry–Howard form (statement as return type) for inductive propositions.
- **Alternatives:**
  - *Propositions as types throughout* (`Eq<Plus<a, b>, Plus<b, a>>`): uniform, but hard to read.
  - *Statement as a separate predicate referenced with `typeof`*: fully type-level, but one extra function per theorem.

### D13. Where theorems live — **Decided** (2026-11-02)
- **Chosen:** anywhere, as in Lean: in the same module as the code they are about, or in separate modules. Theorems are ordinary exported (or local) functions.
- **Consequence (Default):** a module containing theorems has a real `import` of the `proofscript` package. The package is tiny, side-effect free and inert; theorems are never called at runtime; bundlers drop both. This relaxes R6 ("no runtime dependency") to: *no ProofScript code ever runs, and production bundles contain none*.
- **Alternatives for that consequence:**
  - *Ambient globals* (`prove`, `by`, … declared globally, with no JS at all): truly zero runtime, since theorem bodies never execute. But globals collide with user names (`by`, `simp`, `cases` are plausible identifiers), and property-testing a theorem then needs a test harness that installs them.
  - *A post-build stripper* (`proofscript build --strip-proofs`) that removes theorem functions from emitted JS: possible later as an option.
  - *Proof-only modules*: zero runtime, but not Lean-like. Rejected by Jordan.

### D14. Attributes (`@[simp]` etc.) — **Default**
- **Chosen:** marker types intersected into a theorem's return type: `Proof & Simp`.
- **Alternatives:** TS decorators (unavailable on plain functions); a registration call `simp.add(thm)` (runtime code); naming conventions (fragile).

### D15. Names of holes and tactics — **Default**
- **Chosen:** Lean's names: `sorry`, `simp`, `omega`, `rfl`, `exact`, `induction`, … ([05](05-lean-correspondence.md)).
- **Alternatives:** TypeScript-flavoured names (`admit`, `assumeTrue`, …). Rejected to keep Lean users and Lean-trained models at home.

### D16. Hypothesis names in tactic proofs — **Default**
- **Chosen:** callbacks whose parameters name constructor fields and induction hypotheses: `induction(xs, { cons: (h, t, ih) => … })`.
- **Alternative:** string names (`intro("h")`) that the checker binds but `tsc` can't see. Kept only for `intro`.

## Semantics

### D17. Numbers — **Default**
- **Chosen:** semantics directed by static type. `number` is IEEE-754 binary64 exactly as JS; `int`/`nat` are proved safe-integer refinements whose spec arithmetic is exact and whose runtime arithmetic carries no-overflow obligations; `bigint` is exact integers.
- **Alternatives:**
  - *Treat `number` as ℝ or ℤ* (most JS verification prototypes): unsound for real programs.
  - *Only floats*: honest, but integer reasoning becomes painful.

### D18. Equality — **Default**
- **Chosen:** `===` always means JavaScript's `===`; propositional equality is `eq(a, b)`; on `int`/`nat`/`bigint`/`boolean`/`string` the two are proved equivalent.
- **Alternative:** give `===` structural meaning in specs. Rejected because spec and runtime meaning would diverge (a top pitfall in prior art).

### D19. Exceptions — **Default**
- **Chosen:** by default a function may throw; postconditions describe normal returns. A `Throws<…>` refinement (or `Throws<never>`) can be added. Reflected (spec-usable) functions must not throw.
- **Alternative:** require proving no exceptions by default (stricter; hurts adoption).

### D20. Termination — **Default**
- **Chosen:** reflected functions and theorems must terminate (structural recursion detected automatically; otherwise `e satisfies Decreases`). Other verified functions prove termination by default, with an opt-out to partial correctness.
- **Alternative:** partial correctness by default. Easier, but then nothing guarantees anything returns.

### D21. Mutation and the heap — **Default**
- **Chosen:** Dafny-style dynamic frames expressed as types: `Reads<typeof a>`, `Modifies<typeof b>` intersected into the return type, and `Old<typeof x>` in postcondition predicates, over a separation-logic model proved sound against the JS semantics.
- **Alternatives:**
  - *Ownership/permissions* (Verus, Prusti): more automation, but TS has no ownership types to build on.
  - *Exposing separation logic directly*: most powerful, steep for users.
  - *Immutable data only*: simplest, too restrictive for real TS.

### D22. Values from unverified code — **Default**
- **Chosen:** opaque to proofs (kernel type `JSVal`) whatever their TS type says. Knowledge comes only from verified validators, user-written runtime checks (narrowing), or tracked `assume` specs.
- **Alternative:** trust TS types at boundaries. Unsound, since `any`, `as` and `.d.ts` files can lie.

### D23. Type classes — **Open**
- Lean relies on type classes (`Decidable`, `Add`, `Ord`, …). Options:
  - ghost instances resolved by the elaborator;
  - TypeScript interfaces passed as dictionaries;
  - no type classes, with ad-hoc built-ins for numbers and strings.
- To decide before the elaborator handles user-defined algebraic structures.

### D24. Assurance levels — **Default**
- **Chosen:** five levels (0 script, 1 contracts, 2 sound, 3 audited, 4 complete), configured in `tsconfig.json` ([02 §9](02-language-design.md#9-assurance-levels-and-adoption)).
- **Alternative:** a single strict mode plus per-file opt-out (simpler, but loses SPARK-style graduated adoption).

## Implementation

### D25. Implementation language — **Default**
- **Chosen:** TypeScript for the kernel, elaborator and tooling. It runs in Node and the browser, and the kernel can eventually be verified in ProofScript itself.
- **Alternatives:** Rust (speed, wasm; possible later for the kernel only), Go (aligned with the TS 7 compiler), Lean (re-use Lean's kernel directly; see D1).

### D26. Front end — **Default**
- **Chosen:** the TypeScript compiler's JavaScript API (6.x) for parsing, name resolution and `tsc`'s types; all of it untrusted.
- **Alternatives:** our own parser (more work, no benefit under D5); the TS 7 native API once 7.1 is stable (faster; a later migration).

## Licensing

### D27. Using Lean's work — **Default**
- Lean 4, Mathlib, lean4export, lean4lean and nanoda are all **Apache-2.0**. Re-implementing Lean's type theory, tactic names, algorithms and export format in our own code is permitted. Ideas, designs and names of tactics are not something the license restricts.
- If we **copy or translate Lean source code** (e.g. port an algorithm line by line, or vendor Lean files), those parts must keep Apache-2.0 terms: include the license text, keep copyright notices and any NOTICE file, and mark our modifications. Apache-2.0 code can be combined with this repository's MIT license.
- **Trademark:** "Lean" is a trademark of the Lean FRO. Descriptive use ("Lean-compatible kernel", "exports proofs that Lean re-checks") is fine. Anything implying ProofScript is official, affiliated or endorsed is not, without permission.
- **Alternative:** relicense ProofScript as Apache-2.0 or dual MIT/Apache-2.0 (as Rust does), which simplifies mixing in Lean-derived code and adds Apache's explicit patent grant. Worth considering before the first release.
