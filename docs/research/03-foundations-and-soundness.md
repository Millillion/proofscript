# 03 — Foundations and Soundness for ProofScript

*Research report. Status: recommendation, not a final decision. Date: 2026-11-02.*

ProofScript is meant to be a superset of TypeScript with dependent types and formal verification: "Lean, but TypeScript." The design constraints pull against each other:

- **C1 (superset).** Every TS program stays a valid ProofScript program.
- **C2 (erasure).** Constructs specific to ProofScript erase to plain TS/JS. The compiled output must equal what you get by stripping the TS.
- **C3 (incrementality).** Users adopt it file by file in codebases full of `any`, mutation, exceptions, `async`, prototypes, unsound TS types, and untyped npm packages.
- **C4 (genuine soundness).** A proved theorem must be true of the program that actually runs.

This report works out which foundation can satisfy all four, and gives the cost of each choice. The short answer is in §9. Each other section ends with a **Verdict**.

---

## 0. The central insight: three distinct soundness questions

"Sound" means three different things here. Most confusion in this design space comes from mixing them up.

1. **Logical consistency (S-logic).** The kernel cannot prove `False`. This is a property of the core calculus plus its axioms (§1).
2. **Adequacy (S-adequacy).** If the logic says a function `f̂` satisfies `P`, then the JavaScript that actually runs, `strip(f)`, satisfies `P` too. This is a property of how logical terms relate to JS execution (§2, §5, §7). The de Bruijn criterion does **not** cover it. A kernel can check a proof about `f̂` perfectly and still say nothing about `strip(f)`, if the map from source to kernel term (the "reflection" or "elaboration") is wrong.
3. **Robustness (S-robust).** Adequacy has to keep holding when the verified code is linked with arbitrary, adversarial, unverified JS: npm packages, `any`-typed code, monkey-patched built-ins (§3, §4).

Lean, Coq and Agda solve (1) very well. Lean users mostly get (2) for free, because the program *is* the kernel term and the compiler is trusted. They rarely face (3). ProofScript is the reverse case. The program is TS source whose meaning is fixed by ECMAScript, not by the kernel. Most of the hard design work is in (2) and (3).

---

## 1. Core calculus

### 1.1 Candidates

| Family | Representatives | Type checking | Power | Kernel cost |
|---|---|---|---|---|
| Intensional, impredicative `Prop`, CIC | Lean 4, Coq/Rocq | Decidable in practice; Lean's theory is undecidable in principle (below) | Very high: inductive families, universes, quotients, classical logic optional | Small. Lean kernel is a few thousand lines of C++, plus independent checkers |
| Intensional, predicative MLTT | Agda | Decidable; normalization provable | High; no impredicative `Prop` (Agda adds `Prop`/`SProp` variants) | Small; but Agda's checker is not built as a small kernel |
| Extensional TT (equality reflection) | NuPRL, Andromeda | **Undecidable**; derivations must be stored | Very high; funext and UIP for free | Derivation checker can be small, but terms alone are not checkable |
| Refinement types + SMT | Liquid Haskell, F\* (partly), Dafny, Verus | Decidable *relative to SMT*, by limiting the logic to decidable theories | Medium–high with reflection | SMT solver (≈10⁵–10⁶ LOC) plus VC generator in the TCB |

**CIC/Lean.** Lean 4's logic has a non-cumulative universe hierarchy, an impredicative `Prop` with *definitional* proof irrelevance, inductive families with recursors, primitive quotients, and three standard axioms: `propext`, `Quot.sound`, `Classical.choice` (de Moura & Ullrich, CADE 2021, <https://lean-lang.org/papers/lean4.pdf>). Lean's own guidance on validating a proof is to run `#print axioms` and confirm only that trio appears; anything else, including `sorryAx`, signals an incomplete proof or a custom axiom (<https://lean-lang.org/doc/reference/latest/ValidatingProofs/>). Function extensionality is a *theorem*, derived from `Quot.sound`.

**Known metatheoretic quirks of Lean's theory.** Carneiro's thesis *The Type Theory of Lean* (CMU 2019, <https://github.com/digama0/lean-type-theory>) proves the theory consistent, relative to ZFC with inaccessible cardinals. It also shows negative results: in principle, definitional equality as specified is undecidable and the algorithmic check is not transitive, and subject reduction fails. Definitional proof irrelevance combined with subsingleton elimination (for example `Acc`) is what breaks things. Abel & Coquand show the general phenomenon: impredicativity plus a proof-irrelevant *propositional equality* breaks normalization ("Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality," LMCS 2020, <https://arxiv.org/abs/1911.08174>). They also note that consistency and canonicity are unaffected. None of this threatens **consistency**. It means "type checking is decidable" holds in practice, not in theory. For ProofScript this is acceptable: S-logic (consistency) is what matters, and the kernel may reject or time out on pathological terms without harming soundness.

**Coq's alternative.** Coq gets definitional proof irrelevance in a separate sort, `SProp`, and keeps it well behaved by restricting eliminations (Gilbert, Cockx, Sozeau, Tabareau, "Definitional Proof-Irrelevance without K," POPL 2019, <https://doi.org/10.1145/3290316>). MetaCoq has *verified* a type checker and erasure for most of Coq's kernel, PCUIC (Sozeau et al., "Coq Coq Correct!", POPL 2020, <https://metarocq.github.io/coqcoqcorrect>). That is the gold standard for kernel trust, but it is a very large effort.

**Predicative MLTT (Agda).** Agda has cleaner metatheory: normalization is provable for the predicative core. It lacks a widely used small-kernel or independent-checker ecosystem. Impredicative `Prop` is very convenient for specifications ("a predicate on `T` is a `T → Prop`, and `Prop` is closed under ∀ over anything"). It costs nothing in consistency strength that matters for program verification.

**Extensional TT (NuPRL: <https://www.nuprl.org/book/>; Andromeda: Bauer et al., <https://arxiv.org/abs/1802.06217>).** Equality reflection makes type checking undecidable. The kernel then checks *derivations*, not terms, which bloats certificates and complicates tooling. Its main attraction is funext and convenient reasoning about quotients. CIC gets both via quotients plus `propext`. Extensionality would mainly help an SMT-heavy architecture where the solver supplies the equalities, and that puts the SMT solver in the TCB anyway.

**Refinement types + SMT** (Liquid Types: Rondon, Kawaguchi, Jhala, PLDI 2008, <https://doi.org/10.1145/1375581.1375602>; refinement reflection: Vazou et al., POPL 2018, <https://arxiv.org/abs/1711.03842>). Gives excellent automation and a very low annotation burden. But:
- The TCB includes the SMT solver, its theory encodings, and the VC generator.
- The logic is either restricted (QF-EUFLIA plus uninterpreted functions) or made richer by axiomatizing reflected definitions. Axiomatization brings the classic consistency pitfalls: a reflected non-terminating function `f x = f x + 1` axiomatizes `False`. Liquid Haskell had to add termination checking to stay sound under laziness (Vazou et al., "Refinement Types for Haskell," ICFP 2014, <https://doi.org/10.1145/2628136.2628161>).
- No higher-order, inductive, or universe-polymorphic reasoning comparable to CIC.

There is directly relevant prior art: refinement types for TS/JS already exist. See DJS (Chugh, Herman, Jhala, OOPSLA 2012, <https://goto.ucsd.edu/~rjhala/papers/dependent_types_for_javascript.html>) and Refined TypeScript (Vekris, Cosman, Jhala, PLDI 2016, <https://arxiv.org/abs/1604.02480>). They show that SMT-based refinements scale to real JS idioms, but neither aimed at a foundational trust story.

### 1.2 What a Lean-style kernel actually needs

- **Term language.** Variables (de Bruijn), sorts with universe levels, Π, λ, application, `let`, constants, literals (Nat/String, with GMP-accelerated Nat in Lean), projections.
- **Declarations.** Axioms, definitions, theorems, opaque constants, inductive families (with nested/mutual handling), recursors, quotient primitives.
- **Definitional equality.** β, δ, ζ, ι (recursor), η for functions and for structures, proof irrelevance for `Prop`, and unit-like η.
- **Size.** The Lean 4 kernel is a few thousand lines of C++; one secondary source estimates ~5k (<https://arxiv.org/pdf/2604.18882>). The de Bruijn criterion holds: tactics, elaborators, `simp`, and automation are untrusted, because they produce kernel terms that are re-checked (see the unofficial but careful *Type Checking in Lean 4*, <https://ammkrn.github.io/type_checking_in_lean4/>).
- **Independent checkers already exist:**
  - Lean4Lean, an external checker written in Lean and partially verified against a Lean metatheory spec. It runs about 20–50% slower than the C++ kernel, has checked Mathlib, and found a soundness bug (Carneiro, <https://arxiv.org/abs/2403.14064>).
  - nanoda, a Rust kernel (<https://arena.lean-lang.org/checker/nanoda/>).
  - Lean's `comparator` tool, which cross-checks exported proofs with multiple kernels (<https://reservoir.lean-lang.org/@leanprover/Comparator>).
- **Pitfalls.** `implemented_by`, `partial`, and `unsafe` are where Lean's *compiled* semantics can diverge from its logic. A 2026 exploit smuggled an unsafe definition into a proof via `implemented_by` and got it past a third-party checker. The fix was to reject unsafe and partial constants (<https://leanprover-community.github.io/archive/stream/270676-lean4/topic/SafeVerify-passing.20kernel.20soundness.20exploit.html>). The same issue becomes central for ProofScript (§2, §6).

### 1.3 Automation without trusting SMT

To get Dafny/Liquid-level ergonomics without putting Z3 in the TCB, use SMT/SAT as an **untrusted oracle that emits certificates**, which are then reconstructed or checked in the kernel. Examples:
- SMTCoq (Armand et al., CPP 2011, <https://doi.org/10.1007/978-3-642-25379-9_12>).
- `lean-smt` (<https://github.com/ufmg-smite/lean-smt>).
- Lean's `bv_decide`, which checks LRAT certificates from a SAT solver with a verified checker.

Proof-by-reflection (decision procedures written and proved correct *inside* the logic, then run by kernel reduction) is the other standard route. It is especially apt for linear arithmetic over `Int`/safe integers and for finite string and enum reasoning.

### 1.4 Verdict

Use a **CIC kernel whose theory is exactly Lean 4's (LeanTT)**:
- universe-polymorphic Π, inductive families, impredicative definitionally-proof-irrelevant `Prop`;
- quotients, `propext`, funext as a theorem;
- `Classical.choice` allowed but tracked, and restricted to erased positions (§7).

Make the kernel term format *exportable to Lean's kernel export format*, so that Lean, Lean4Lean, nanoda and comparator can serve as independent checkers from day one. ProofScript may ship its own small kernel, written in TS for tooling convenience. It should never be the *only* checker.

This gives:
- the best known power/trust ratio;
- an existing ecosystem of independent re-checkers (a much stronger de Bruijn story than any new design can reach quickly);
- the option of importing Mathlib-style libraries for the mathematical side (reals, floats, finite maps).

SMT is used only through certificate checking or proof reconstruction.

---

## 2. The two-world problem: logic vs. JavaScript

The logic is pure, total, and terminating. JavaScript is effectful, partial, mutable, and dynamically typed, and it runs in an environment the program does not control. We need a precise relation between them. Four families of approaches exist.

### 2.1 (a) A reflected pure, total fragment

Examples:
- ACL2: the logic *is* a pure subset of Common Lisp (<https://www.cs.utexas.edu/~moore/acl2/>).
- Dafny `function`s (Leino, LPAR 2010, <https://doi.org/10.1007/978-3-642-17511-4_20>).
- Verus `spec fn`s, with a mode system (`spec`/`proof`/`exec`) where specs are exempt from linearity checks and proven terminating (Lattuada et al., OOPSLA 2023, <https://arxiv.org/abs/2303.05491>).
- Liquid Haskell refinement reflection (above).

**Soundness obligation.** The reflection map `R : TSFragment → KernelTerm` must satisfy an **adequacy** lemma: for every value `v` in the fragment's domain, running `strip(f)` on `⟦v⟧_JS` yields `⟦R(f) v⟧_JS`, or exhausts a resource (§5.4).

In every one of these systems the reflection or translation is **trusted**:
- Dafny trusts its compilers.
- Verus trusts its erasure and Rust's compiler.
- F\* trusts extraction.
- Aeneas trusts its translation; Ho, Fromherz & Protzenko later note there was no formal argument for the original translation and set out to provide one (<https://arxiv.org/pdf/2404.02680v1>).

Merits:
- Great ergonomics: the *same* TS function is both the program and the specification.
- Proofs are about real code.
- It requires purity and totality, and data restricted to immutable values with a clean model.

### 2.2 (b) Program logics for imperative code

- Hoare logic / weakest preconditions.
- Separation logic (SL) for aliasing and the heap:
  - Iris: higher-order concurrent SL in Coq (Jung et al., JFP 2018, <https://doi.org/10.1017/S0956796818000151>).
  - VST: C, in Coq.
  - Viper: an intermediate verification language over SMT (Müller, Schwerhoff, Summers, VMCAI 2016, <https://doi.org/10.1007/978-3-662-49122-5_2>).
  - Gillian: parametric symbolic execution with SL, instantiated to JS and C (Fragoso Santos et al., PLDI 2020, <https://www.doc.ic.ac.uk/~pg/publications/FragosoSantos2020Gillian.html>; extended at <https://arxiv.org/abs/2105.14769>).
- Dijkstra monads in F\*: specs as predicate transformers, derived "for free" by a CPS translation of the effect's monad (Ahman et al., POPL 2017, <https://arxiv.org/abs/1608.06499>; Swamy et al., POPL 2016, <https://doi.org/10.1145/2837614.2837655>).
- Hoare Type Theory / Ynot: Hoare triples as a monadic type inside a dependent type theory (Nanevski, Morrisett, Birkedal, ICFP 2006, <https://doi.org/10.1145/1159803.1159812>; Chlipala et al., ICFP 2009, <https://doi.org/10.1145/1596550.1596565>).

Merits:
- Required for code with shared mutable state, aliasing, and interaction with untrusted code.
- SL's frame rule is what makes local reasoning possible in a world where any callback could mutate anything.

### 2.3 (c) Monadic shallow embedding

Imperative code is translated into a functional program in a monad, and verified with the logic's ordinary tools:
- Aeneas translates *safe* Rust (exploiting borrow discipline) into pure functions with "backward functions" for mutable borrows, and has a Lean backend (Ho & Protzenko, ICFP 2022, <https://arxiv.org/abs/2206.07185>; <https://lean-lang.org/use-cases/aeneas>).
- Lean's own `do`-notation with `StateM`/`ExceptT`/`Id`, verified with the `mvcgen` (now `vcgen`) monadic VC generator over `Std.Do` Hoare triples (<https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/>).
- Interaction trees (ITrees) give a coinductive free-monad representation of impure, possibly non-terminating, interacting programs, with an equational theory up to weak bisimulation (Xia et al., POPL 2020, <https://arxiv.org/abs/1906.00046>).

Merits:
- Reuses the kernel. Specifications are ordinary propositions.
- Local mutation (`let` reassignment, loops over local arrays) is free: it becomes `StateM` or plain fold/recursion.
- It breaks down for *unrestricted aliasing*. TS has no borrow checker, so Aeneas's trick (purity derived from ownership) does not apply in general. In the general case we need an explicit heap model, and SL on top of it.

### 2.4 (d) Runtime contracts at boundaries

- Higher-order contracts with blame (Findler & Felleisen, ICFP 2002, <https://doi.org/10.1145/581478.581484>).
- "Well-typed programs can't be blamed" (Wadler & Findler, ESOP 2009, <https://homepages.inf.ed.ac.uk/wadler/papers/blame/blame.pdf>).
- Typed Racket's sound migratory typing (Tobin-Hochstadt & Felleisen, POPL 2008, <https://doi.org/10.1145/1328438.1328486>).

Merits:
- The *only* way to say anything sound about values produced by unverified code.
- Costs runtime overhead and changes behavior: new exceptions are raised. That tension with C2 is resolved in §4.

### 2.5 Verdict: use all four, each in its own layer

| Layer | Code kind | Technique | Lives in |
|---|---|---|---|
| **Pure** | Total functions over immutable data | (a) reflection, with a proven-adequate reflection map | Kernel definitions |
| **Local-imperative** | Functions with local mutation, loops, early return, `throw`, no escaping aliases | (c) monadic shallow embedding (state + exceptions), Lean-`do`-style VCs | Kernel definitions in a `JS` monad |
| **Heap-imperative** | Shared mutable objects, callbacks, async | (b) SL/WP over a JS heap model, ITrees for external interaction and `await` | Kernel, via a WP/SL library *proved sound* against the JS-subset semantics |
| **Untrusted** | `any`, npm, unannotated TS | (d) validators/contracts with blame, or explicit `assume` | Runtime checks plus axioms tracked in trust footprints |

The key architectural rule is that **(b), (c), and (d) are not new trusted mechanisms**. Each is a *library inside the kernel*, proved sound against a single deep-embedded semantics of a JS subset (§5). Only that semantics, plus the reflection and adequacy theory relating it to source, is foundational. This is how Iris-, VST- and CakeML-style stacks keep the TCB small.

---

## 3. Gradual verification and gradual dependent types

### 3.1 The literature

- **Gradual program verification** (Bader, Aldrich, Tanter, VMCAI 2018, <https://link.springer.com/content/pdf/10.1007%2F978-3-319-73721-8_2.pdf>). Derived by the Abstracting Gradual Typing methodology (Garcia, Clark, Tanter, POPL 2016, <https://doi.org/10.1145/2837614.2837670>). A specification may be *imprecise* (`? ∧ P`). Statically provable parts are proved; the rest is checked at runtime. Follow-ups:
  - recursive heap structures with implicit dynamic frames (Wise et al., OOPSLA 2020);
  - **Gradual C0**, built on Viper's symbolic execution (DiVincenzo et al., <https://arxiv.org/abs/2210.02428>);
  - a formal soundness proof of gradual verification via symbolic execution (Zimmerman, DiVincenzo, Aldrich, POPL 2024, <https://jennalwise.github.io/assets/pdf/zimmerman2024soundgv.pdf>);
  - pure-function support (<https://arxiv.org/pdf/2511.22075>).

  **The soundness notion is dynamic.** A gradually verified program either satisfies its specifications, or a runtime check fails. It is not a theorem that the specification holds.
- **Gradual refinement types** (Lehmann & Tanter, POPL 2017, <https://www.dcc.uchile.cl/TR/2016/TR_DCC-20161107-001.pdf>). Imprecise refinements `{x:Int | ?}` and `{x | P ∧ ?}`, with runtime checks justified by abstract interpretation. The guarantee is again "type-safe up to dynamic check failure."
- **Approximate normalization** (Eremondi, Tanter, Garcia, ICFP 2019, <https://arxiv.org/abs/1906.06469>). Dependent type checking must *run* code, but gradual code may diverge or fail. They split compile-time normalization (approximate, total) from runtime execution (exact, may fail or diverge). Extended to inductive families in <https://arxiv.org/abs/2107.04859>.
- **GCIC** (Lennon-Bertrand, Maillard, Tabareau, Tanter, TOPLAS 2022, <https://arxiv.org/abs/2011.10618>). The **Fire Triangle of Graduality**: a gradual CIC cannot simultaneously have
  1. **conservativity** over CIC,
  2. **normalization** (hence decidable checking, and the usual logical reading), and
  3. **graduality** (the dynamic gradual guarantee: losing precision does not change behavior except by removing errors; Siek et al., SNAPL 2015, <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SNAPL.2015.274>).

  GCIC offers three variants, each giving up one edge.
- **Dependent interoperability** (Dagand, Tabareau, Tanter, JFP 2018, <https://www.cambridge.org/core/journals/journal-of-functional-programming/article/abs/foundations-of-dependent-interoperability/801E5D733DE9BC30B1A34A5FDC621242>). Relates dependently typed values to simply typed ones via *partial type equivalences / Galois connections*, with runtime checks for the partial direction. This is exactly the *boundary* problem, solved without making the logic itself gradual.

### 3.2 What the Fire Triangle implies for ProofScript

1. **A gradual dependent type theory is not a logic.** In GCIC the unknown term `?_A` inhabits every type, including `False`. Closed proofs of `False` reduce to `?` or `err`, which is the "weak canonicity" GCIC proves. That is fine for a *programming* language. It is fatal for a *proof* language, because a "theorem" proved using `?` asserts nothing.
2. **So `any` must never enter the kernel as a type.** It cannot be a type consistent with all types in the kernel's sense. TS's `any` is precisely the gradual unknown type, compounded by TS's unsoundness.
3. **Graduality (C3) and normalization/conservativity (C4) must be split across layers.** The logic (kernel) stays fully static: CIC, normalizing in practice, conservative. Graduality lives only at the program layer, where imprecision is *discharged by runtime checks at boundaries*, never by the kernel accepting `?`. This is the "dependent interoperability" architecture, not the "gradual CIC" architecture.
4. **Gradual verification is still useful, with a clear meaning.** ProofScript can offer Bader-style imprecise specifications at the program layer. The resulting guarantee is **"P holds, or a runtime check raises blame"**, the same shape as §4's boundary theorem. Theorems (`theorem` declarations) and kernel-verified specs remain fully static. The UI must make the distinction visible:
   - "verified": statically, no runtime residue;
   - "checked": verified modulo inserted runtime checks;
   - "assumed": an axiom.
5. **Erasure (C2) vs. inserted checks.** Gradual verification inserts runtime checks, so the output is no longer the TS-stripped output. Resolution: ProofScript never *inserts* checks implicitly. Every runtime check is ordinary user-visible TS: a call to a validator function, such as a generated `isFoo(x)` or `parseFoo(x)`, or a contract wrapper. The checker *requires* the check before it accepts a fact about an untrusted value. This keeps C2 exact: compile = strip. The tool can offer a quick-fix that writes the check into the source.

**Verdict.** No gradual kernel. A static CIC logic, plus *explicit*, user-visible runtime checks at boundaries whose correctness is itself proved in the kernel, plus imprecise specs only as a program-layer convenience with a "P or blame" guarantee.

---

## 4. Trust boundaries with unsound TS types

### 4.1 TS types cannot be trusted

TypeScript is unsound by design. Bierman, Abadi & Torgersen catalogue the deliberate unsoundnesses: bivariant method parameters, `any`, unchecked casts, covariant arrays, and more ("Understanding TypeScript," ECOOP 2014, <https://gavinbierman.github.io/assets/pdf/ecoop2014.pdf>). In addition:
- `.d.ts` declarations for npm packages are unchecked claims;
- the type system is Turing-complete and depth-limited (<https://github.com/microsoft/TypeScript/issues/14833>).

**Hence ProofScript's soundness must never depend on the judgement `tsc ⊢ e : T`.** At most it can be a hint for elaboration.

### 4.2 The design space of boundary semantics

Greenman & Felleisen compare the main options ("A Spectrum of Type Soundness and Performance," ICFP 2018, <https://doi.org/10.1145/3236766>):

| Semantics | Example | Guarantee | Cost |
|---|---|---|---|
| **Erasure / optional** | TypeScript | None at runtime ("trust the declarations") | Zero |
| **Transient** | Reticulated Python (Vitousek, Swords, Siek, POPL 2017, <https://www.cs.cornell.edu/projects/tpls/papers/20170210.shtml>) | First-order *shape* checks at elimination sites; open-world soundness for type *constructors* only | Low |
| **Natural / guarded** | Typed Racket | Full type soundness with blame; higher-order values wrapped | Can be severe (Takikawa et al., "Is Sound Gradual Typing Dead?", POPL 2016, <https://www.khoury.northeastern.edu/home/asumu/artifacts/popl-2016>) |
| **Concrete / nominal checks** | Safe TypeScript (Rastogi et al., POPL 2015, <https://doi.org/10.1145/2676726.2676971>), StrongScript/"Concrete types for TypeScript" (Richards et al., ECOOP 2015, <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2015.76>) | Soundness for the checked fragment with cheap tag checks | Low–moderate; changes semantics |
| **Axiomatic** | Liquid Haskell `assume`, Lean `axiom`/`sorry` with `#print axioms` | Soundness *relative to* the assumptions, which are auditable | Zero runtime; trust is explicit |

Transient is insufficient for dependent refinements. Checking `typeof x === "number"` says nothing about `x > 0 ∧ isSafeInteger(x)`, let alone a relational property of a function argument. Natural/guarded is sound but costly for higher-order values, and its wrappers change object identity, which is observable in JS via `===` and WeakMap keys.

### 4.3 Recommended semantics: a value model, plus three explicit trust modes

**The logical value model.** The kernel contains an inductive `JSVal`:

```
undefined | null | bool b | number (f : Float64) | bigint (i : Int)
| string (s : List UInt16) | symbol (id) | object (loc)
```

Objects live in a heap `Heap := Loc ⇀ ObjRecord`. A **ProofScript type `T` has a semantic interpretation `El T : JSVal → Heap → Prop`**, a unary realizability predicate. Every ProofScript claim about a runtime value is a claim through `El`.

**Every value that originates in unverified code has logical type `JSVal` and nothing more**, whatever its TS type says. To learn more, the verified code must use one of three trust modes. Each mode is visible in source and recorded in the declaration's **trust footprint**.

1. **`validate` (first-order data; sound, no axioms).** A user-written, or tool-generated and committed, TS function `parseT(x: unknown): T | undefined`. It is itself verified, with the kernel theorem `parseT x = some y → El T y`.

   Crucially, the validator **copies in**. It reads the untrusted structure once and builds a fresh, owned, frozen or unaliased value. Two reasons:
   - JS objects from unverified code can change after validation, because the producer may keep an alias (TOCTOU).
   - Getters and Proxies can return different values on each read.

   Validating *the copy* makes the theorem true regardless of what the adversary does later or what traps fire during the read. This is how zod/io-ts *should* be used. Generated validators are ordinary TS, so C2 holds.
2. **`contract` (higher-order: callbacks, objects with methods, promises).** A wrapper in the Findler–Felleisen style: argument checks on entry, result validation on exit, blame labels. Facts about results of wrapped functions hold *conditional on no blame*. The theorem shape becomes "P or blame(C)". Wrapping is again explicit user code, such as `const f = wrap(contractOf<F>(), untrustedF)`. The wrapper library is verified once.
3. **`assume` (axiom; zero runtime cost; explicitly trusted).** For example, `assume declare function sha256(b: Bytes): Bytes32 ensures ...`, or `assume lodash.sortBy is stable`. These become kernel axioms *about the JS model*: predicates on behaviours in the ITree/heap semantics, not on kernel functions. That keeps the logic consistent even when an assumption is *false at runtime*: a false assumption makes the conclusion vacuous, never makes `False` provable in the base logic. Each theorem's footprint lists the assumptions used, analogous to `#print axioms` (`ps audit --axioms`). One rule follows directly: an `assume` must never be stated as an equation between a *kernel* function and something inconsistent (`assume f x = f x + 1`). Restricting assumptions to the form "this external behaviour satisfies predicate Q in the JS semantics" guarantees *relative* consistency: the model always exists, by interpreting unknown behaviours as any trees satisfying Q, provided Q is satisfiable. The tool can demand a satisfiability witness for Q. If Q is unsatisfiable, every theorem relying on it is vacuous, and the audit flags it.

**Compare with the alternatives.**
- "Trust the declarations" (TS) is unsound by definition.
- Liquid Haskell `assume` is equivalent to our mode 3, but LH's assumes can poison the SMT context with contradictory facts. Our restriction to behavioural predicates over a model avoids that.
- Typed Racket's natural semantics corresponds to our mode 2, applied automatically everywhere. We make it explicit and pay only where the user opts in.
- Reticulated's transient semantics we reject as insufficient for refinements.

### 4.4 Robustness against an adversarial environment

Linking with arbitrary JS raises threats that type-boundary checks alone do not address:

- **Intrinsics tampering.** Unverified code can redefine `Array.prototype.map`, `Object.prototype` setters, `Math.max`, `JSON.parse`, `Promise.prototype.then`, and so on. Verified code compiled by stripping calls those intrinsics directly. So adequacy is false unless the intrinsics are intact. Options:
  - require an environment assumption **E-intrinsics**, discharged at runtime by Hardened JavaScript `lockdown()` (SES), which freezes all shared intrinsics (<https://github.com/endojs/endo/blob/HEAD/packages/ses/README.md>);
  - or snapshot "primordials" at module load (Node's internal technique). Snapshotting would change emitted code; to keep C2, it must be written by the user.

  A middle path: verified code may only call intrinsics through a small, verified `ps-runtime` module of captured primordials, written as ordinary TS imports.
- **Escape of internal state.** Verified mutable objects reachable by the adversary can be mutated behind the verifier's back. Require ownership discipline: objects handed to unverified code must be (i) fresh copies, (ii) `harden()`ed (deep-frozen), or (iii) covered by an SL invariant the adversary cannot break, for example only *opaque capability* objects (closures). The checker enforces this statically; the user writes the `harden` call.
- **Reentrancy.** Callbacks into unverified code can re-enter verified code. SL invariants must be re-established before every call-out, exactly as in object-capability verification.

The right proof technique is **robust safety via a logical relation**, as in Swasey, Garg & Dreyer's Iris-based OCPL (OOPSLA 2017, <https://people.mpi-sws.org/~dg/papers/oopsla17-obj-full.pdf>). Untrusted code is modelled as *any* code that is semantically well-typed at the "low" or `any` interpretation. A fundamental lemma shows every syntactically untyped program inhabits that interpretation. This gives a theorem quantifying over *all* adversaries.

There is a gap: our semantics covers only a JS subset S (§5), and the adversary may use all of JS (`eval`, `Proxy`, `with`). Close it with an **interface semantics**. The adversary's only interaction with verified code is through the values it receives (hardened objects, copies, closures) and the values it passes in, which are validated, contracted, or assumed. So the adversary can be modelled abstractly as an arbitrary ITree over the boundary interface, *without needing a semantics of the adversary's own code*. Soundness then depends on a precise **encapsulation assumption**: in real JS, the adversary cannot reach verified state except through those interfaces. With frozen intrinsics and hardened exports this is the standard SES/object-capability guarantee. It is an *assumption* about JS engines and SES, and it belongs in the TCB (§9.3).

**Verdict.** The kernel never trusts TS types. Untrusted values enter as `JSVal`. Knowledge about them comes only from (1) verified copy-in validators, (2) verified contract wrappers ("or blame"), or (3) tracked behavioural axioms. Environment integrity (frozen intrinsics, hardened exports) is an explicit, checkable environment assumption.

---

## 5. Formal semantics of JavaScript

### 5.1 State of the art

| Work | Coverage | Mechanized | Executable / tested | Notes |
|---|---|---|---|---|
| λJS (Guha, Saftoiu, Krishnamurthi, ECOOP 2010, <https://cs.brown.edu/~sk/Publications/Papers/Published/gsk-essence-javascript>) | ES3 via desugaring to a small core | PLT Redex | Tested against Mozilla suite | Desugaring is the trusted part |
| S5 (Politz et al., DLS 2012, <https://doi.org/10.1145/2384577.2384579>) | ES5 strict incl. getters/setters, `eval` | Redex-style | Tested (test262 subset) | Core + desugar approach |
| JSCert / JSRef (Bodin et al., POPL 2014, <https://www.doc.ic.ac.uk/~pg/publications/Bodin2014Trusted.html>) | ES5 core, pretty-big-step | Coq | JSRef is extracted and proved correct w.r.t. JSCert, run on test262 | Libraries mostly missing in the original work |
| KJS (Park, Ştefănescu, Roşu, PLDI 2015, <https://fsl.cs.illinois.edu/publications/park-stefanescu-rosu-2015-pldi.html>) | ES5.1, passes all 2,782 core test262 tests | K framework | Executable, symbolic | Found bugs in V8, SpiderMonkey, WebKit |
| JaVerT 2.0 (Fragoso Santos et al., POPL 2019, <https://www.doc.ic.ac.uk/~pg/publications/FragosoSantos2019JaVerT.html>) / Gillian-JS | ES5 strict via JSIL | Partially | SL-based verification and bi-abduction | Compiler JS→JSIL validated by test262 |
| ECMA-SL / ECMARef5/6 (IST Lisbon, <https://fenix.tecnico.ulisboa.pt/downloadFile/1689244997263330/ECMA_SL_Extended_Abstract.pdf>) | ES5, ES6 | Intermediate language, not a proof assistant | Tested on test262 | Closest to modern ES |
| WasmCert-Coq/Isabelle (Watt et al., FM 2021, <https://www.cl.cam.ac.uk/~jp622/two_wasm.pdf>) | Wasm 1.0 complete | Coq + Isabelle | Verified interpreter, official tests | Shows a full mechanization is feasible when the language is small |

**Lessons.**
1. Full modern ECMAScript (ES2025: modules, async, generators, Proxy, Reflect, TypedArrays, the Intl surface) has never been fully mechanized in a proof assistant. It is huge: thousands of spec pages' worth of algorithm steps.
2. The successful pattern is a **small core semantics plus desugaring**, or **mechanized semantics plus an extracted reference interpreter, differentially tested against test262 and real engines** (JSCert/JSRef, KJS, WasmCert). Testing is what makes a mechanized spec *trustworthy*, since the spec cannot be proved equal to an English document.

### 5.2 A tractable subset S ("ProofScript Core JS")

Verified code, meaning everything whose behavior a theorem speaks about, must be written in a subset S:

- strict-mode ES modules; `let`/`const`; functions and arrows; closures; `if`/`switch`/loops/`break`/`continue`/labelled statements;
- `throw`/`try`/`catch`/`finally`;
- object and array literals, property get/set on *own data properties* of objects created by verified code; `class` without accessor properties or dynamic `super` tricks, modelled as records plus a fixed prototype;
- primitives: `number`, `bigint`, `string`, `boolean`, `undefined`, `null`;
- `Map`/`Set` with SameValueZero keys; promises and `async`/`await`, modelled via ITrees with a job queue (later phase).

**Excluded from S** (they may appear only in unverified code):
- `eval`, `new Function`, `with`, `arguments` aliasing, sloppy mode;
- `Proxy`, `Reflect` mutation;
- getters/setters on verified objects; `__proto__` and `setPrototypeOf`;
- `Symbol.toPrimitive`/`valueOf` on verified objects;
- implicit coercions on operands whose type is not statically primitive (forbid `==`, require primitive operands for `+`, `<`, and so on, so ToPrimitive never runs user code);
- `delete` on verified records; sparse arrays and holes;
- `SharedArrayBuffer`/`Atomics`, workers, `FinalizationRegistry`/`WeakRef` (non-deterministic GC observation).

These are exactly the features that make JSCert and KJS large. Removing them from *verified* code (not from the language) leaves a semantics comparable to a small ML with records, exceptions, and a mutable heap: within WasmCert/CakeML scale. Restricting implicit coercion to primitives is especially important. ECMAScript's `ToPrimitive` calls `valueOf`/`toString`/`@@toPrimitive`, which can run arbitrary code inside an innocent-looking `a + b`.

### 5.3 Making "compiled JS behaves as the logic says" a theorem

Plan:
1. **Deep-embed S in the kernel:** syntax, a big-step or ITree semantics, a heap, and the value model of §4.3. Write it to mirror the ES spec's algorithm steps where possible (JSCert's lesson), so reviewers can compare clause by clause.
2. **Extract or compile an executable interpreter** from the embedded semantics (JSRef's lesson). Run it differentially against test262 (filtered to S) and against V8, SpiderMonkey, and JavaScriptCore on generated programs (KJS's lesson: this finds engine bugs and spec-model bugs).
3. **Prove once, generically, in the kernel:**
   - *Reflection adequacy:* for every pure-fragment function `f`, `eval_S (strip f) ⟦v⟧ ⇓ ⟦R(f) v⟧`, or a resource error.
   - *Monadic embedding adequacy:* the `JS`-monad shallow embedding of a local-imperative function is equal to `eval_S` of its stripped body.
   - *WP/SL soundness:* the program logic is sound for `eval_S`.
4. **Translation validation of the frontend.** The TS parser/elaborator is large and should not be trusted. Make it untrusted. Take the *actually emitted* JS (the stripped file) and re-parse it with a *small, separately audited* parser for S into the deep-embedded AST. Check that this AST is the one the kernel proofs are about (syntactic equality after normalization). The TCB then shrinks to: the S-parser (small), the embedded semantics (reviewed and tested), and the kernel. This mirrors CompCert's use of validated parsers (Leroy, CACM 2009, <https://doi.org/10.1145/1538788.1538814>).

With this, "compiled JS behaves as the logic says" becomes a **kernel theorem**, conditional only on: *the engine implements S as modelled* (an empirical claim supported by test262 and differential testing), plus the environment assumptions of §4.4.

### 5.4 Resource bounds

A logically total function can still fail in JS:
- stack overflow (`RangeError: Maximum call stack size exceeded`) on deep recursion;
- `Invalid string length` (V8 caps strings at about 2²⁹ code units);
- array length limits, BigInt size limits, out-of-memory.

The adequacy statement must be **"returns the logical value, or fails with a resource-exhaustion error"**. This is exactly CakeML's end-to-end theorem shape: the program behaves as specified *or runs out of memory* (Kumar et al., POPL 2014, <https://doi.org/10.1145/2535838.2535841>). A resource error must never be catchable in a way that lets verified code continue in a state the logic considers impossible. So: `try/catch` inside verified code must not catch resource errors and then rely on invariants. The simplest rule is that a verified `catch` treats all exceptions as possible at every call. Users who need stack-safety guarantees can prove a recursion-depth bound and rely on an assumed minimum stack budget, which is explicit in E.

### 5.5 Numbers, BigInt, strings

**Float64.**
- Coq has Flocq, a comprehensive IEEE-754 library used by CompCert (Boldo & Melquiond, ARITH 2011, <https://doi.org/10.1109/ARITH.2011.40>).
- Lean 4's `Float` now has a logical model: `Float.Model`, a subtype of `UInt64` that canonicalizes NaN. Arithmetic and comparisons are defined *on the model* and replaced by native doubles at compile time. Transcendental functions are opaque. The documentation advises building a richer library on a separate model and transferring lemmas (<https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/>).

**Recommendation for `number`.**
- Model as **binary64 bit patterns**, with `+ − × ÷`, `%` (ES remainder: truncating, *not* IEEE remainder), `sqrt`, comparisons, and conversions defined *exactly* by IEEE 754 roundTiesToEven, the way ECMAScript requires.
- NaN: ES exposes NaN bit patterns only through TypedArrays/DataView, and only as implementation-defined, so model NaN *as a single value* at the `number` level. Handle bit-level views as a nondeterministic choice in the semantics.
- Distinguish `−0`. Model `===`, `Object.is`, and SameValueZero separately.
- **`Math.sin`, `exp`, `log`, `pow` (in part), and so on are "implementation-approximated"** in the ECMAScript spec (<https://tc39.es/ecma262/#sec-function-properties-of-the-math-object>). They **must** be uninterpreted functions, with only the guarantees the spec states (special cases for NaN/±0/±∞). Never give them a definitional value: `Math.sin(1)` really differs between engines.
- Integer views: `Int53 := { x : Float64 // Number.isSafeInteger x }`, with a verified isomorphism to `{ n : Int // |n| ≤ 2⁵³−1 }`. Key lemmas: `+`, `−`, `*` on `Int53` whose exact result stays within the safe range are exact and agree with `Int`. `Math.floor(a / b)` is exact integer floor-division for `Int53` (with `b ≠ 0`); this needs proof, and holds because correctly rounded division followed by floor is exact for |a| < 2⁵³. Bitwise operators go through `ToInt32`/`ToUint32` and should be modelled as `Int32`/`UInt32` bit-vector ops. With this refinement, most "number used as an integer" code becomes verifiable with integer reasoning, and that is most real code.

**`bigint`** maps to `Int`, with ES semantics: `/` and `%` truncate toward zero; `>>` is floor; `BigInt.asIntN` and `asUintN` are explicit. Size limits are resource errors.

**`string`** is a `List UInt16` (UTF-16 *code units*; lone surrogates are legal). `length`, indexing, and `<` are code-unit based. `codePointAt` and iteration (`for…of` yields code points) are defined functions. `toLowerCase`/`toUpperCase`/`normalize`/`localeCompare` depend on the engine's Unicode/ICU version. Keep them uninterpreted, or parameterize them by an assumed Unicode version.

**Other implementation-defined or non-deterministic behaviour** must be modelled as nondeterminism or uninterpreted:
- `Array.prototype.sort` with an inconsistent comparator (ES2019 requires stability, but an inconsistent comparator gives an implementation-defined order);
- `Date.now`, `Math.random`, `crypto.*`;
- property enumeration order is now mostly specified (integer keys ascending, then insertion order), so it can be modelled exactly for the subset S.

**Verdict.** A mechanized semantics of a well-chosen subset S, deep-embedded in the kernel and differentially tested, is feasible at roughly WasmCert/CakeML-semantics scale. It is what turns adequacy from an assumption into a theorem. Stage it: start by trusting a reviewed reflection translation (as Dafny and Verus do), and grow the semantics and adequacy proofs underneath without changing the user-facing language.

---

## 6. Termination and totality

### 6.1 Mechanisms

- **Structural recursion.** Compiled to recursors or checked via the structural-recursion elaborator (Lean, Coq).
- **Well-founded recursion with `decreases`/`termination_by`** (Dafny, Lean, Verus). The measure and proof are erased; the runtime code is the plain recursive function. Adequacy holds because `WellFounded.fix` satisfies the unfolding equation, so the JS recursion and the logical function compute the same values.
- **Fuel.** An extra `Nat` argument. Not erasure-compatible if the fuel affects control flow. Avoid it in the source language; keep it only as a proof technique.
- **Delay / partiality monads.** Capretta's coinductive Delay (LMCS 2005, <https://doi.org/10.2168/LMCS-1(2:1)2005>). Its quotient by weak bisimilarity, constructed as a QIIT (Altenkirch, Danielsson, Kraus, FoSSaCS 2017, <https://www.cse.chalmers.se/~nad/publications/altenkirch-danielsson-kraus-partiality.html>). ITrees generalize Delay with events.
- **Lean `partial def`.** Elaborated to an *opaque* constant implemented by an unsafe auxiliary. It requires the type to be `Inhabited`, because otherwise the opaque constant would be an axiom of an empty type. The kernel knows nothing about its body. Sound, but nothing can be proved about the function.
- **Lean `partial_fixpoint`.** Recursive definitions in a monad with a chain-complete partial order (CCPO), for example `Option`, are defined as least fixpoints of monotone functionals. They get real equations, plus a `fixpoint_induct` / `partial_correctness` principle (<https://lean-lang.org/doc/reference/latest/Recursive-Definitions/Partial-Fixpoint-Recursion>). This is the right tool for **partial correctness of possibly non-terminating code**.

### 6.2 Coexistence with general TS

Rules that keep the logic consistent:

1. **Only total functions become kernel functions of pure type.** The pure fragment (§2.5) requires structural recursion or a proved `decreases` measure. The default is to try automatic measures (structural, `length`, lexicographic) and fall back to a user annotation.
2. **Possibly non-terminating verified code** (event loops, `while(true)` servers, search with unknown bounds) is reflected **in the `JS` monad**, never as a pure function. The `JS` monad's CCPO/ITree structure gives the definition meaning via `partial_fixpoint`-style least fixpoints, and supports partial-correctness and invariant reasoning. Divergence is an *observable behaviour* in the semantics (an infinite `Tau` sequence), not a logical contradiction.
3. **Unverified TS functions are never reflected.** In the logic they are external behaviours: uninterpreted events in the ITree semantics, constrained only by `assume` or contracts. They never need termination proofs, and they cannot be inconsistent, because they are not equations in the logic.
4. **Never axiomatize the defining equation of an unverified recursive function.** That is the classic route to `False` (`f x = f x + 1`). Lean avoids it with opacity; LH/Dafny avoid it with termination checks. ProofScript avoids it structurally: there is no pathway from an unverified function to a kernel equation.
5. **Total correctness in the monad** (terminates *and* satisfies Q) is available through a WP with a variant, for code that wants it.

**Verdict.** Three tiers: total pure (kernel functions); possibly divergent but verified (least-fixpoint definitions in the `JS` monad, partial correctness, optional total correctness); and unverified (opaque external behaviours). Lean's `partial def` opacity trick is *not needed* for unverified code, because unverified code is never in the logic as a function at all. It is useful only as an escape hatch inside verified modules ("this is in my verified file, but I give up on proving anything about it").

---

## 7. Erasure

### 7.1 Theory

- **Quantitative Type Theory.** McBride ("I Got Plenty o' Nuttin'," 2016) and Atkey (LICS 2018, <https://strathprints.strath.ac.uk/64031>; Atkey's version fixes a substitution issue in McBride's). Bindings are annotated with multiplicities in a semiring {0, 1, ω}. Quantity-0 variables may appear only in types and other quantity-0 positions, so they are provably erasable. Idris 2 uses QTT as its core and relies on it for erasure (Brady, ECOOP 2021, <https://arxiv.org/abs/2104.00480>).
- **Agda run-time irrelevance `@0`.** Similar, enforced by a modality (<https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html>).
- **Lean/Coq.** Types and `Prop` proofs are erased by the compiler. Soundness of erasure rests on the *elimination restriction*: a `Prop` can be eliminated into `Type` only if it is a syntactic subsingleton (`Eq`, `And`, `True`, `False`, `Acc`). So runtime computation can never branch on proof data. MetaCoq has *verified* type-and-proof erasure for Coq (POPL 2020, above). Coq's extraction (Letouzey, TYPES 2002, <https://doi.org/10.1007/3-540-39185-1_12>) does the same for program extraction.
- **Verus modes** (`spec`/`proof`/`exec`) and **F\*'s `GTot`/`erased`** give the same discipline in verification languages.

### 7.2 A precise erasure criterion for ProofScript

A ProofScript construct is **erasable** iff it occupies a *ghost position*, defined by the following rules:

- **G1 — Sort positions.** Any type-level term (its type is a sort `Type u`/`Prop`). TS already erases these (generic parameters, annotations).
- **G2 — Proof positions.** Any term whose type is a `Prop`: proofs, `assert` justifications, lemma applications, `decreases` arguments.
- **G3 — Ghost bindings (quantity 0).** Parameters, `let`s, fields, and return components marked `ghost`. The checker enforces the QTT rule: a ghost variable may be used only in G1/G2/G3 positions.
- **G4 — Elimination restriction.** Runtime code may pattern-match or branch on a value only if that value is runtime-relevant. Matching on a ghost value or a proof is allowed only into ghost/proof results, or when the eliminated type is a subsingleton (as in Lean).
- **G5 — No runtime type inspection of erased types.** No `typeof T`-style case analysis over generic parameters. TS's own semantics already forbids this, and it is what makes generics parametric.
- **G6 — Classical choice and other noncomputable axioms** may be used only in G1–G3 positions. Lean's `noncomputable` check plays this role.

**The second half of C2: compile = strip.** ProofScript syntax must be designed so that every ghost construct is removed by a **syntactic type-stripping pass of the `erasableSyntaxOnly` kind**. That is the class of TS syntax that tools like Node's type stripping (Amaro), ts-blank-space, and TS 5.8's `--erasableSyntaxOnly` can remove without changing runtime semantics (<https://www.typescriptlang.org/docs/handbook/release-notes/typescript-5-8.html>). Concretely:
- Proof blocks, theorems, `requires`/`ensures`, invariants, `decreases`, and ghost parameters all live in syntactic positions that strip to nothing.
- Ghost *arguments* at call sites must be removed too. So ghost parameters must be syntactically marked at *both* declaration and call site, or be positioned as a trailing erasable clause.
- Refinement types `{x: number | x > 0}` and subtypes erase to their carrier (`number`). The runtime representation of a subtype is the value itself, as with Lean's `Subtype` under proof erasure.
- Proof-carrying records must use `declare`-style or type-only fields. A real class field initializer would survive stripping.
- ProofScript must *reject* TS's non-erasable runtime syntax (enums, namespaces with values, parameter properties) only *inside verified regions*, where it needs a semantic model of them. Elsewhere it accepts them, to satisfy C1.

**Theorem to prove (Erasure correctness).**
- (i) *Syntactic:* `emit(M) = strip(M)` byte-for-byte, modulo whitespace and comments. This is checkable per build by running a reference stripper and diffing, so the ProofScript emitter is not trusted.
- (ii) *Semantic:* for the kernel term `t` elaborated from `M`, `erase(t)` corresponds to `parse_S(strip(M))`, and `erase` preserves evaluation. This is the MetaCoq-style erasure correctness theorem, specialized to our semantics.

Combining (i), (ii), the translation validation of §5.3, and adequacy (§2) gives the end-to-end statement.

**Verdict.** Use QTT-style 0-multiplicity plus Lean's Prop-elimination restriction as the *type-theoretic* erasure criterion. Use `erasableSyntaxOnly`-style syntactic strippability as the *syntactic* criterion. Prove the two coincide, and validate it per build by diffing against an independent stripper.

---

## 8. TS type-level features vs. genuine dependent types

### 8.1 What TS types are

- **Literal types and unions of literals.** Singleton and finite-set refinements: `"a" | "b"` ≈ `{ s : string // s = "a" ∨ s = "b" }`.
- **Object types.** *Structural, open* (width subtyping), with optional properties, index signatures, and `readonly` (which is not enforced against aliases). The semantic reading is a predicate on `JSVal`/heap ("has own or inherited property `k` whose value satisfies `El T_k`"), not a closed record type.
- **Generics.** Erased, parametric-ish (unchecked casts break parametricity). Natural reading: Π over a universe of type *codes* with quantity 0.
- **Conditional types `A extends B ? X : Y`.** Branch on *assignability*. Assignability is TS's subtyping, which is unsound, partly heuristic, and depth-limited. They distribute over unions, and `infer` performs unification.
- **Mapped and template literal types, `keyof`, indexed access.** Computation over type codes and string-literal sets (regular languages).
- **`typeof x` (type query).** Takes the *static* type of a value. It is not a dependent type: it never depends on a runtime value.
- **Overall.** Turing-complete (<https://github.com/microsoft/TypeScript/issues/14833>), with no normalization guarantee beyond recursion limits, and unsound (§4.1).

So TS's type-level language is a **dynamically checked, untyped functional language over type codes**, whose base predicate (assignability) is unsound. It has no value-dependency. TS types can mention only literal values, never program variables or terms like `n + 1`.

### 8.2 Can TS types get a principled interpretation in the core?

Yes, for a fragment, via a **Tarski-style universe of codes**:

```
inductive TSTy : Type
| num | str | bool | big | undef | null
| lit (v : Lit) | union (a b : TSTy) | inter (a b : TSTy)
| obj (fields : List (Key × Opt × TSTy)) (index? : Option TSTy)
| arr (t : TSTy) | tuple (ts : List TSTy) | fn (dom : List TSTy) (cod : TSTy)
| refine (t : TSTy) (p : JSVal → Prop) -- ProofScript extension
| var (i : Nat) ...
def El : TSTy → JSVal → Heap → Prop
```

Then:
- generics are quantification over `TSTy` (or over arbitrary predicates);
- `keyof` and mapped types are ordinary total functions on codes;
- template literal types are regular-language predicates on strings;
- conditional types become functions on codes, **provided `extends` is reinterpreted using a *sound and decidable* subtyping relation `≤` proved to satisfy `t ≤ u → ∀v h, El t v h → El u v h`**.

Where `≤` can't decide (higher-order, recursive types), the conditional type stays "stuck" in the logic and nothing is concluded. Function types under `El` need the contract/realizability reading ("for all inputs satisfying `El dom`, any behaviour of the function satisfies ...") over the ITree semantics.

### 8.3 What ProofScript should do

1. **TS types are an untrusted documentation and inference layer.** `tsc` keeps running unchanged, which preserves C1 and the existing ecosystem. Its verdicts never contribute to soundness.
2. **ProofScript types are kernel types.** For first-order data in the pure fragment, the elaborator translates the TS annotation through `TSTy`/`El` *where it can*: literal types, unions, discriminated unions, readonly records, tuples, arrays as immutable lists, `number` → `Float64` (or `Int53` when refined), `bigint` → `Int`. These become genuine inductive or subtype kernel types. Discriminated unions map onto inductive types, the most valuable correspondence.
3. **Fallback.** Where translation is not possible (conditional types over `any`, deep type-level computation), the value has kernel type `JSVal` plus whatever its `El` predicate yields after evaluating the code-level function, *if that evaluation terminates in the kernel*. Otherwise just `JSVal`.
4. **Genuine dependent types** (`Vec n`, `{ i : Int53 // i < xs.length }`, `ensures result = sum xs`) are ProofScript extensions that strip to the carrier TS type. TS's generics plus literal types are useful as *surface syntax* for the simplest cases: `Tuple<3>`-style types interpret as `Vec 3`.
5. **Never import a TS type-level computation as an axiom** ("tsc says this conditional type reduces to `X`, so assume it"). TS's reduction is unsound and implementation-defined.

**Verdict.** Interpret a well-behaved fragment of TS types semantically, as predicates on a JS value model via a universe of codes, with ProofScript's own sound subtyping. Treat everything else, and all of `tsc`'s judgements, as untrusted documentation. Don't try to give TS's full type-level language a faithful dependent interpretation: it has no sound interpretation to be faithful to.

---

## 9. Recommended foundation

### 9.1 Layered architecture

**Layer K — Kernel (the trust root).**
- CIC exactly as in Lean 4 (LeanTT): universe-polymorphic Π, inductive families, impredicative definitionally-proof-irrelevant `Prop`, quotients, `propext`; funext as a theorem; `Classical.choice` allowed only in erased positions.
- Terms exportable in Lean's kernel export format. Every release, and optionally every CI run, re-checks with ≥2 independent kernels (Lean C++, nanoda/Lean4Lean) via a comparator-style harness.
- No `unsafe`, `implemented_by`, or `partial` constants are admitted in theorem dependencies (the 2026 SafeVerify lesson).
- Automation (SMT/SAT, `omega`-like procedures, simp) is untrusted and produces kernel-checked proofs or certificates.

**Layer M — Mechanized JS model (inside K).**
- `JSVal`, `Heap`, `Float64` (bit-exact IEEE-754 with ES's operations; implementation-approximated `Math.*` uninterpreted), `Int` for BigInt, `List UInt16` strings.
- Syntax and ITree-based semantics of the subset **S** (strict ESM, no eval/with/Proxy/accessors/prototype mutation/implicit object coercion in verified code; async via an event-loop job-queue model in a later phase).
- An extracted reference interpreter for S, differentially tested against test262 and major engines.

**Layer P — Logic fragment ("pure ProofScript").**
- Total, pure TS functions over immutable data (records, discriminated unions, readonly arrays/tuples, `number`/`Int53`, `bigint`, `string`).
- Reflected as kernel definitions, with termination by structure or `decreases`.
- Specifications and proofs written in ProofScript syntax, all in ghost positions (G1–G6).
- *Adequacy theorem:* reflection agrees with `eval_S` on the stripped code, modulo resource exhaustion.

**Layer I — Imperative verified code.**
- *Local-imperative:* monadic shallow embedding into a `JS` monad (state, exceptions, CCPO least fixpoints for possibly-divergent loops), with a `vcgen`-style VC generator.
- *Heap-imperative, callbacks, async:* a WP/separation-logic library (Iris-lite: points-to, invariants, frame rule, object capabilities) proved sound *inside K* against Layer M's semantics.

**Layer B — Boundaries with unverified code.**
- Unverified values have kernel type `JSVal`. Unverified functions are opaque external behaviours (ITree events), never kernel functions.
- Knowledge flows in only through:
  1. verified copy-in validators (first-order, no runtime trust);
  2. verified contract wrappers with blame (higher-order; "P or blame");
  3. behavioural `assume`s (axioms about external behaviours; zero cost; tracked).
- All checks are explicit, user-visible TS code, so compile = strip.
- Optional gradual-verification ergonomics (imprecise specs with checks the tool proposes, which the user then writes explicitly).

**Layer E — Environment assumptions (stated, checkable where possible):**
- E1. Intrinsics are not tampered with: run under SES `lockdown()`, or verified code uses only a captured-primordials module.
- E2. Values exported to unverified code are copies, hardened, or opaque capabilities (statically enforced).
- E3. The engine implements S as modelled (empirical, via differential testing).
- E4. Single-threaded heap: no `SharedArrayBuffer` sharing with verified state.
- E5. Resource errors are fatal or treated as possible at every call (no "impossible" states after catching them).

**Trust tracking.** Every theorem and spec carries a *trust footprint*: the kernel axioms used (`propext`, `Quot.sound`, `choice`), every `assume`, every contract whose blame is excluded, and the E-assumptions relied on. `ps audit` prints it (the `#print axioms` analogue). A "fully verified" badge requires footprint ⊆ {standard axioms} ∪ {E1–E5}.

### 9.2 The soundness theorem we would eventually prove

Fix a program `𝒫 = M₁ … Mₙ ⊕ C`, where `Mᵢ` are ProofScript modules that check, and `C` is arbitrary JavaScript: npm packages, unverified TS, adversarial code, possibly outside S. For each spec `φ` proved in some `Mᵢ`, let its trust footprint be `A_φ`.

> **Theorem (End-to-end soundness, target).**
> Assume:
> - (K) LeanTT with the standard axioms is consistent, and the kernel and its independent re-checkers accepted the proofs;
> - (E) the environment satisfies E1–E5;
> - (A) every behavioural assumption in `A_φ` holds of the actual external code.
>
> Then every execution of `strip(M₁) … strip(Mₙ)` linked with `C` on a conforming engine either
> - (i) satisfies `φ`, as interpreted in Layer M via `El` and the trace semantics; or
> - (ii) halts with **blame** at a contract or validator boundary, and blame is never assigned to any `Mᵢ`; or
> - (iii) halts with a **resource-exhaustion** error.
>
> In addition, `emit(Mᵢ) = strip(Mᵢ)` (syntactic erasure), so the deployed artifact is exactly the TS-stripped program.

**Proof sketch.**
1. Translation validation gives the deep-embedded AST of `strip(Mᵢ)` equal to the AST the kernel reasons about.
2. Adequacy of reflection and of the monadic embedding, plus soundness of the WP/SL library w.r.t. `eval_S`, give `φ` for executions where all boundary interactions satisfy their contracts.
3. A robust-safety logical relation (Swasey–Garg–Dreyer style) shows that adversary `C` can affect verified state only through boundary interfaces. Validators are verified, contracts raise blame on violation (Blame theorem, Wadler–Findler), and assumptions hold by (A). Encapsulation follows from E1/E2 under the object-capability reading of hardened JS.
4. Resource errors are a separate observable outcome in the semantics (CakeML shape).
5. Kernel acceptance of the proofs yields truth of `φ` in the model by consistency of LeanTT.

### 9.3 Trusted computing base

| Component | Size / nature | Mitigation |
|---|---|---|
| Kernel(s) | A few kLOC | ≥2 independent checkers; LeanTT consistency proved in Carneiro's thesis; Lean4Lean verification ongoing |
| Layer M semantics of S (faithfulness to ECMAScript) | Several kLOC of definitions | Written to mirror spec steps; extracted interpreter; test262 plus differential testing; community review |
| S-subset parser used for translation validation | Small | Independent implementation; fuzzing against a reference JS parser |
| Reference TS stripper (for `emit = strip`) | Existing tool (Amaro/ts-blank-space/tsc) | Diffing; two strippers |
| JS engine conformance for S | Huge (V8 etc.) | Unavoidable; empirical; restrict S to well-trodden features |
| SES/lockdown, or primordials capture (E1) | Moderate | Widely audited; or a verified primordials module |
| User `assume`s | User-controlled | Footprints, audit, satisfiability witnesses |

**Not in the TCB:** the ProofScript elaborator, type checker, TS frontend, tactics, SMT solvers, VC generators, the WP/SL library (proved sound in K), validators and contracts (verified), and `tsc`.

### 9.4 Phasing (keeps the end-state theorem reachable)

1. **Phase 1.**
   - Kernel = LeanTT with Lean export.
   - Pure fragment with a *trusted* reflection, reviewed and simple (the Dafny/Verus position).
   - Validators and assumes; erasure check by diffing.
   - Float64/Int53/BigInt/string models.
   - Trust footprints from day one.
2. **Phase 2.**
   - Deep-embedded semantics of S, an extracted interpreter, and differential testing.
   - Translation validation of emitted JS.
   - Adequacy proofs for the pure fragment, which removes reflection from the TCB.
3. **Phase 3.**
   - `JS` monad with local-imperative VCs.
   - WP/SL library proved sound; contracts with blame; robust-safety theorem for the boundary.
4. **Phase 4.** `async`/promises via ITrees and a job-queue model, classes and prototypes in S, and broader library models (Map/Set/Array methods) proved against the semantics.

### 9.5 Main open risks

1. **Semantic faithfulness of S.** The theorem is only as good as the model of ECMAScript and of engines. JIT bugs and spec misreadings are real; KJS found bugs in all three major engines. This is mitigated by testing, not by proof.
2. **Environment integrity (E1/E2) in real deployments.** Many apps cannot run under SES `lockdown()` because legacy libraries mutate built-ins. Without E1, adequacy for any code that touches intrinsics is unsupported. The fallback (captured primordials) is safe but intrusive in the source.
3. **Adequacy and robust-safety proof effort.** This is CakeML/Iris-scale engineering. Until Phase 2–3 lands, the reflection is trusted, which is honest but weaker.
4. **Usability under the Fire Triangle.** Because `any` cannot flow into proofs, adoption friction concentrates at boundaries. Validators and contracts must be generated well, and copy-in has performance costs (cf. Typed Racket's overheads).
5. **Higher-order contracts change identity.** Wrappers break `===` and WeakMap keys. Contracts must be opt-in, and their identity effects must be in the model.
6. **Async and reentrancy.** Interleavings at `await` points and reentrant callbacks require invariant-based SL reasoning, which is notoriously hard for users. Expect most early verification to target pure and local-imperative code.
7. **Implementation-approximated and environment-dependent built-ins** (`Math.*`, Unicode case mapping, `Intl`, sort with bad comparators). Models must be conservative, which limits what can be proved about numeric/string-heavy code.
8. **LeanTT metatheory quirks.** Undecidable defeq in principle and failure of subject reduction are mostly theoretical, but they constrain any *verified* re-implementation (Lean4Lean). Stay exactly on LeanTT, not a variant, to reuse that work.
9. **Resource exhaustion.** Stack depth in particular. Users may be surprised that "total" verified recursive functions crash on large inputs. Lint for non-tail deep recursion, and optionally offer depth-bounded specs.
10. **Language evolution.** New TS syntax and new ES features must be either excluded from S or modelled, and new TS erasable syntax must keep `emit = strip` checkable.

---

## Appendix: one-paragraph summary

Use a **Lean-4-compatible CIC kernel** (impredicative proof-irrelevant `Prop`, inductive families, quotients, tracked classical axioms, multiple independent checkers) as the only logical trust root. Above it, put a **deep-embedded, differentially tested semantics of a JS subset S** with bit-exact Float64, BigInt, and UTF-16 strings. **Reflect pure, total TS** into the kernel with a proven adequacy theorem. Verify **imperative code** through a monadic shallow embedding plus a WP/separation-logic library proved sound against S. Connect **unverified code** only through explicit verified validators (copy-in), contracts with blame, or tracked behavioural `assume`s, never through TS types, and never through a gradual kernel, since the Fire Triangle rules that out. Enforce erasure by QTT-style ghost positions and check `emit = strip` per build. Make every claim carry a trust footprint. The target theorem is: *every execution of the stripped program, linked with arbitrary JS under stated environment assumptions (frozen intrinsics, hardened exports, conforming engine), satisfies the proven spec, or halts with blame on an unverified party, or exhausts resources.*
