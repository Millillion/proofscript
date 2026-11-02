# 02 — Verification Prior Art: A Critical Survey for ProofScript

Status: research note (draft). Date: 2026-11-02.

ProofScript's goal is "Lean, but TypeScript": a superset of TypeScript with dependent types and formal verification. It must work for two audiences: (1) people who write theorems and proofs in TS-like syntax, and (2) people who want to verify properties of ordinary TypeScript programs and adopt it incrementally in existing codebases. Everything must compile to ordinary TS/JS. This note surveys prior systems through that lens. It focuses on the design decisions that matter to us, not on full descriptions of each system.

For each system we look at seven things:

1. **Logic**: the core logic or type theory.
2. **Proofs**: how proofs are written (tactics, terms, or SMT-backed "auto-active" verification).
3. **Specs**: how specifications attach to code.
4. **Exec vs. logic**: how executable code relates to logical code (ghost code, erasure, extraction).
5. **Effects**: effects, mutation, exceptions, partiality, and non-termination.
6. **TCB**: the trusted computing base.
7. **Target, adoption, and lessons**: what it compiles to, and what we can learn from how it was adopted.

---

## 1. Lean 4

**Logic.** Lean 4 uses a variant of the Calculus of Inductive Constructions. It has a non-cumulative universe hierarchy `Sort u`, with an impredicative, definitionally proof-irrelevant `Prop` at the bottom (`Sort 0`). It also has inductive types with structural recursion compiled to recursors, built-in quotient types (`Quot`, with `Quot.sound` as a kernel primitive), and three standard axioms: `propext`, `Classical.choice`, and `Quot.sound` (from which funext is derived). Definitional proof irrelevance means that any two proofs of the same `p : Prop` are definitionally equal. That is what makes subtypes `{x // p x}` cheap and lets proofs be erased. See the [Lean reference manual on types and axioms](https://lean-lang.org/doc/reference/latest/) and [Carneiro, "The Type Theory of Lean"](https://github.com/digama0/lean-type-theory/releases).

**Proofs.** Lean supports both term-mode proofs (lambda terms) and tactic proofs (`by ...`). Tactics are ordinary Lean programs running in the `TacticM`/`MetaM` monads. Since Lean 4, the whole elaborator, the macro system, and the tactic framework are written in Lean and can be extended by users ([Ullrich & de Moura, "Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages", IJCAR 2020/LMCS 2022](https://arxiv.org/abs/2001.10490); [de Moura & Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021](https://lean-lang.org/papers/lean4.pdf)). The automation is substantial:

- `simp`: a rewriting engine driven by `@[simp]` lemma sets.
- `omega`: a decision procedure for linear integer and natural-number arithmetic.
- `decide`: evaluates a `Decidable` instance in the kernel.
- `norm_num`, `ring`, `linarith`, `positivity`, `aesop` (from Mathlib and the ecosystem).
- `grind`, released in v4.22 (Aug 2025): an SMT-inspired tactic that does congruence closure and E-matching over `@[grind]`-annotated lemmas, with built-in theory solvers including "cutsat" (which supersedes `omega` and constructs models) and a Gröbner basis solver ([v4.22.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)). Every one of these tactics produces a proof term that the kernel re-checks. This is the key difference from Dafny/F*-style SMT trust.

**Specs.** Specs are types. A function's signature can carry dependent types, subtypes, or a separate `theorem foo_spec : ∀ x, P (foo x)`. For imperative `do`-code, specs are usually stated about the pure denotation. Newer work adds Hoare-style program logics on top of monads: `Std.Do`/`mvcgen` in core (2025), plus external frameworks such as Velvet and Loom, which LemmaScript uses as its Lean backend (see §7).

**Exec vs. logic.** There is one language. Lean's compiler erases `Prop`s, types, and other irrelevant arguments, then lowers through LCNF/IR to C (and from there to native code). Several escape hatches separate execution from logic:

- `partial def`: compiles normally, but the kernel sees an opaque constant. The only requirement is that the return type be `Inhabited`, which keeps the logic consistent. Nothing about the function's behaviour can be proven.
- `unsafe`: allows anything but cannot be used from safe code, except through `implemented_by`.
- `@[implemented_by f]`: the kernel reasons about the reference definition, while compiled code runs `f`. The two are trusted to agree. This is a classic pattern ("reference model for proofs, fast impl for runtime"), and also a soundness hole if misused.
- `@[extern]`: FFI, trusted.
- `noncomputable`: a definition (for example one using `Classical.choice`) that the logic accepts but that has no code.

Well-founded recursion (`termination_by`/`decreasing_by`) gives total functions with proofs. They compile efficiently, but they reduce poorly in the kernel because they are irreducible by default.

**Effects.** `do`-notation over monads (`IO`, `StateM`, `ExceptT`, `ST`). It supports local mutable variables, `for` loops, `return`, `break`, and `continue`, all desugared to pure monadic code ([Ullrich & de Moura, "do Unchained", ICFP 2022](https://dl.acm.org/doi/10.1145/3547640)). This is directly relevant: TS-style imperative syntax can be elaborated into a pure functional core. At runtime, arrays use reference counting with destructive updates when the count is 1 ("Counting Immutable Beans", [Ullrich & de Moura, IFL 2019](https://arxiv.org/abs/1908.05647)), so pure code over arrays gets in-place performance.

**TCB.** The kernel (a C++ type checker) plus the three axioms. The compiler is *not* trusted for logical soundness, but it is trusted for "compiled code matches its definition". Native code that uses `native_decide` (via `Lean.ofReduceBool`) extends the TCB to the compiler, which is why Mathlib bans it. Independent checkers re-check exported proofs:

- [lean4lean](https://arxiv.org/abs/2403.14064) (Carneiro): a Lean kernel reimplemented and partly verified in Lean. It found a real soundness bug.
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib): a Rust checker.
- `lean4checker`: replays environments.

The kernel is small, the elaborator is huge, and automation is untrusted. This is the de Bruijn criterion done well.

**Target.** C, through Lean's own IR. A JS backend has been experimented with, but nothing official exists.

**Adoption lessons.**

- Mathlib (over 2M lines) shows that a single, unified, centrally curated library plus strong metaprogramming makes formal mathematics scale. Its maintenance burden is real: there is constant refactoring, and versions are pinned to Lean toolchain releases.
- Lean's "functional programming language that is also a prover" framing (the *Functional Programming in Lean* book) brought in programmers.
- The weak spots are verifying effectful code, kernel performance on well-founded recursion, and the steep learning curve of dependent type errors.
- Lean has become the default substrate for AI theorem proving (§9), and that is a strategic asset.

## 2. Idris 2

**Logic.** Quantitative Type Theory (QTT) ([Atkey, "Syntax and Semantics of Quantitative Type Theory", LICS 2018](https://bentnib.org/quantitative-type-theory.pdf); [McBride, "I Got Plenty o' Nuttin'", 2016](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)). Every binder carries a multiplicity: 0 (erased, usable only in types), 1 (linear, used exactly once at runtime), or ω (unrestricted). Idris 2 is not consistent as a logic by default, since `partial` functions and `believe_me` exist. Totality checking is opt-in per function (`total`) or per module (`%default total`).

**Proofs.** Mostly terms, with holes, interactive case-splitting, and proof search (`auto` implicits, `%search`). Elaborator reflection exists, but tactics are much weaker than in Lean or Coq.

**Exec vs. logic.** This is the key lesson for ProofScript. Erasure is *typed*: an argument at quantity 0 is guaranteed erasable, and the type checker rejects any runtime use of it. There is no separate erasure analysis and there are no erasure surprises ([Brady, "Idris 2: Quantitative Type Theory in Practice", ECOOP 2021](https://arxiv.org/abs/2104.00480)). Type parameters, indices, and proofs are written `{0 n : Nat}` or `(0 prf : LTE a b)`. Linearity (quantity 1) supports safe in-place mutation and resource protocols.

**Effects.** `IO` is a monad. Linear types handle resource protocols, and an effects library exists.

**Target.** Chez Scheme by default, plus Racket, Gambit, **JavaScript and Node**, and RefC (C). Idris 2's JS backend is a real precedent for compiling an erased dependently typed language to JS.

**Lessons.** Explicit 0-multiplicities are clean but syntactically noisy. Idris infers 0 for implicit type-level arguments in many places, and ProofScript should do the same so users rarely write quantities by hand. Idris has stayed a research/teaching language, partly because its ecosystem and tooling are small. Elegant foundations alone don't produce adoption.

## 3. Agda

**Logic.** Martin-Löf type theory with a universe hierarchy, inductive and inductive-recursive families, and dependent pattern matching (with `--without-K` and `--cubical` options). Its termination checker uses size-change/structural analysis.

**Proofs.** Terms only: interactive holes, case-split, auto (Agsy/Mimer), and reflection-based macros. No tactic language to speak of.

**Exec vs. logic.** Compiles to Haskell (MAlonzo) and **JavaScript** (`agda --js`). Erasure comes from `@0`/`@erased` run-time irrelevance annotations, a QTT-inspired feature added in Agda 2.6 ([Agda docs: Run-time irrelevance](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html)). `Prop` is a definitionally proof-irrelevant sort.

**Lessons.** Agda's Unicode-heavy mixfix syntax is beloved by experts and alienating to everyone else. Its JS backend has always been an afterthought, with no performance work. Holes-driven interactive development is excellent UX that ProofScript's LSP should copy: type-directed hole filling, case-splitting, and goal display.

## 4. Coq / Rocq

**Logic.** pCIC: the Calculus of Inductive Constructions with an impredicative `Prop`, a predicative `Set`/`Type` hierarchy, and since 8.10 `SProp` (definitionally proof-irrelevant propositions; [Gilbert et al., "Definitional Proof-Irrelevance without K", POPL 2019](https://hal.inria.fr/hal-01859964)). Coq was renamed **Rocq** in 2025 ([rocq-prover.org](https://rocq-prover.org)).

**Proofs.** Ltac (and Ltac2) tactic scripts, plus SSReflect, plus `lia`/`nia`/`ring`/`micromega`. Automation includes CoqHammer and SMTCoq (which checks SMT certificates).

**Exec vs. logic: extraction.** Extraction ([Letouzey, "A New Extraction for Coq", TYPES 2002](https://www.irif.fr/~letouzey/download/extraction2002.pdf)) erases `Prop` and types and produces OCaml, Haskell, or Scheme. The `Prop`/`Set` split *is* the erasure discipline: anything in `Prop` is logically irrelevant and erased. That is also why large elimination from `Prop` into `Set` is restricted, since computational content must not depend on erased proofs. Extraction is *not verified*. MetaCoq's verified erasure ([Sozeau et al., "The MetaCoq Project", JAR 2020](https://metacoq.github.io/); "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq", JACM 2025) and CertiCoq (to C) narrow this gap. Extracted OCaml uses `Obj.magic` to escape OCaml's weaker type system, which is a precedent for "emit untyped-ish host code where the host type system can't express dependent types". ProofScript will need the same: emit `any`/casts where TS's types can't express the dependent ones.

**Major uses.** CompCert, Fiat-Crypto (verified code that Chrome/BoringSSL actually ship, extracted to C), Iris (concurrent separation logic framework, foundational for later Rust work), the Four Color Theorem, and Feit–Thompson.

**Lessons.** Proof maintenance across Coq versions has historically been painful (`Ltac` brittleness, unstable automation). Extraction plus a separate runtime language works for "verified core, unverified shell" systems, but it creates a *two-languages* problem that an integrated design like ProofScript can avoid.

## 5. F*

**Logic.** A dependently typed, higher-order language with refinement types and a lattice of user-definable monadic effects ([Swamy et al., "Dependent Types and Multi-Monadic Effects in F*", POPL 2016](https://www.fstar-lang.org/papers/mumon/)). The base effects are:

| Effect | Meaning |
|---|---|
| `Tot` | Total, pure, terminating |
| `GTot` | Ghost total. May use ghost (erased) values, so cannot be used at runtime |
| `Pure pre post` | Total, with a Hoare-style spec |
| `Div` | Possibly divergent. Partial correctness only. *Cannot appear in specs or types*, which is the key soundness trick |
| `ST`/`Stack`/`Heap` | Stateful, with heap pre/postconditions (HyperStack memory model for Low*) |
| `Exn`, `All` | Exceptions, and everything combined |

Effects are ordered (`Tot ≤ Pure ≤ Div ≤ ...`; `Ghost` sits beside them), and lifting is automatic. Specs are computed by weakest-precondition calculus in a Dijkstra monad ([Swamy et al., "Verifying Higher-order Programs with the Dijkstra Monad", PLDI 2013](https://www.microsoft.com/en-us/research/publication/verifying-higher-order-programs-with-the-dijkstra-monad/); [Maillard et al., "Dijkstra Monads for All", ICFP 2019](https://arxiv.org/abs/1903.01237)). Erased values are `erased t` (`FStar.Ghost`).

**Proofs.** The type checker generates verification conditions (VCs), and Z3 discharges them. When SMT fails, users add lemma calls (proofs as ordinary unit-returning functions with `Lemma` effect, e.g. `val lemma_foo : x:nat -> Lemma (ensures P x)`), `assert`s, or Meta-F* tactics ([Martínez et al., "Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms", ESOP 2019](https://arxiv.org/abs/1803.06547)). Tactics are F* programs in the `Tac` effect, which mixes tactic-produced and SMT-discharged goals. **Pulse** (2024–25) adds a concurrent separation logic DSL embedded in F*.

**Exec vs. logic.** Extraction to OCaml, F#, and C (via KaRaMeL for the Low* subset). An older JS backend existed, and there is also a WASM path. `GTot` and `erased` code is erased. Low* ([Protzenko et al., "Verified Low-Level Programming Embedded in F*", ICFP 2017](https://arxiv.org/abs/1703.00053)) is a *shallow embedding of a C-like subset* in F*: you write in F*, and KaRaMeL erases proofs and emits readable C. HACL* ([Zinzindohoué et al., CCS 2017](https://eprint.iacr.org/2017/536)) ships in Firefox, the Linux kernel, Python, and Tezos. EverParse generates verified parsers. Project Everest built HTTPS components.

**TCB.** Large: the F* type checker (not small, written in F*), Z3, the encoding of F* to SMT, and KaRaMeL/extraction. F* is explicitly *not* de Bruijn.

**Lessons.**

- The effect lattice with `Div` forbidden in specs, `Ghost` erased, and `Tot` required for logic is the cleanest known way to embed partial or effectful code in a dependently typed logic without inconsistency. It maps well onto ProofScript's "pure total logical fragment vs. effectful TS" split.
- "Lemmas are just functions returning unit with a postcondition" is a very TS-friendly idiom.
- F*'s usability problems are well known: SMT instability, opaque failures ("could not prove post-condition" with a span), slow verification, and the need to tune `--z3rlimit`, `--fuel`, and `--ifuel`.
- Everest's experience: proof engineers spent much of their time stabilising proofs against Z3 upgrades.

## 6. Dafny

**Logic.** An imperative, object-oriented language with first-order-ish specification constructs: `requires`, `ensures`, `modifies`, `reads`, `decreases`, `invariant`, plus `function` (pure, total, usable in specs), `method` (imperative), `predicate`, `lemma` (a ghost method), `ghost` variables and fields, `seq`/`set`/`map`/`multiset` mathematical types, and `calc` blocks ([Leino, "Dafny: An Automatic Program Verifier for Functional Correctness", LPAR 2010](https://www.microsoft.com/en-us/research/publication/dafny-automatic-program-verifier-functional-correctness/); [Dafny reference manual](https://dafny.org/latest/DafnyRef/DafnyRef)). It translates to Boogie, which generates VCs for Z3. The heap uses dynamic frames.

**Proofs.** "Auto-active" verification: no tactics, the user writes assertions, lemma calls, loop invariants, and `calc` chains, and Z3 fills the gaps ([Leino & Moskal, "Usable Auto-Active Verification", 2010](http://fm.csl.sri.com/UV10/submissions/uv2010_submission_20.pdf)). Lemmas are ghost methods whose bodies are proofs, and induction is written as recursion. This is the most programmer-friendly paradigm we know of. The vericoding benchmark also found LLMs succeed far more often on Dafny than on Lean or Verus (§9).

**Exec vs. logic.** `ghost` is a first-class modifier. Ghost code is checked to have no effect on compiled state and is erased. Before Dafny 4, `function` was ghost by default and `function method` was compiled. In Dafny 4, `function` is compiled and `ghost function` is spec-only. The renaming is itself a lesson: the default matters. **Compile targets: C#, Java, JavaScript, Go, Python, (C++ partial), and Rust** (new in 2024–25). The JS backend shows that verified-imperative-to-JS works. The output, however, is not idiomatic and needs a runtime library (`dafny-runtime`, BigNumber for `int`). `int` is mathematical, which is a JS mismatch (see the numbers discussion in §11). Attributes like `{:verify false}`, `{:axiom}`, `assume`, and `{:extern}` allow incremental and unsafe trust, and `dafny audit` reports them.

**Effects.** `method` can mutate the heap, framed by `modifies`. `function` is pure. There are no exceptions; `:-` handles failure-compatible types (Result-like). `decreases` handles termination (often inferred). `decreases *` marks a possibly non-terminating method that cannot be called from terminating code.

**TCB.** Dafny's translator, Boogie, Z3, and the compilers. Testing the compilers found real bugs ([Irfan et al., "Testing Dafny (experience paper)", ISSTA 2022](https://dl.acm.org/doi/10.1145/3533767.3534382)).

**Adoption.** AWS uses Dafny in production: the authorization engine of AWS IAM ([Zelkova/Cedar](https://www.amazon.science/publications/cedar-a-new-language-for-expressive-fast-safe-and-analyzable-authorization) — Cedar's spec is in Dafny, now moving to Lean), the AWS Encryption SDK, and more. Dafny itself is TS-like enough that "Dafny with TS syntax" is a credible baseline for the program-verification half of ProofScript. Pain points are SMT brittleness, timeouts, `{:vcs_split_on_every_assert}`, the "matching loop" trigger problem, and opaque failures (which is why Dafny added `opaque`/`reveal` and `--isolate-assertions`). Cedar moving from Dafny to Lean (2024) is telling: [AWS reported](https://aws.amazon.com/blogs/opensource/lean-into-verified-software-development/) that Lean's proofs were more stable and faster to check, with interactive control where Dafny's SMT was unpredictable.

## 7. Refinement types: Liquid Haskell, RSC (Refinement Types for TypeScript), Flux

### 7.1 Liquid Haskell

**Logic.** Refinement types `{v:T | p}` with predicates in a decidable SMT logic: QF-UFLIA plus arrays, sets, and bitvectors ([Rondon, Kawaguchi, Jhala, "Liquid Types", PLDI 2008](https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf); [Vazou et al., "Refinement Types for Haskell", ICFP 2014](https://goto.ucsd.edu/~nvazou/icfp14/refinement_types_for_haskell.pdf)). Subtyping becomes Horn constraints, and liquid inference (predicate abstraction over qualifiers) infers loop and recursive invariants. Specs live in `{-@ ... @-}` comments (now also a GHC plugin), which is the "specs in comments, host compiler untouched" incremental-adoption model.

**Refinement reflection and PLE.** In [Vazou et al., "Refinement Reflection: Complete Verification with SMT", POPL 2018](https://arxiv.org/abs/1711.03842), `reflect`ing a terminating Haskell function copies its definition into the logic as an uninterpreted function plus equations. *Proofs are ordinary Haskell functions* returning `Proof = ()`, with refinements stating the theorem. Equational reasoning combinators (`==.`, `***`, `?`) build proofs as programs, and induction is recursion with termination checked. **Proof by Logical Evaluation (PLE)** unfolds reflected definitions automatically, bounded and guaranteed to terminate for decidable fragments, which removes much of the manual unfolding. ["Theorem Proving for All: Equational Reasoning in Liquid Haskell"](https://arxiv.org/abs/1806.03541) (Vazou, Breitner, Kunkel, Van Horn, Hutton; Haskell Symposium 2018) shows Haskell programmers writing textbook proofs in Haskell itself.

This is the model closest in spirit to ProofScript's second audience: **the theorem is a type, the proof is a function, and the function is erased/no-op at runtime**. Because `Proof = ()`, the proof functions are *not* erased. They compile and run as unit functions, which costs runtime and is a known wart. ProofScript should erase them.

**Lessons.** Decidable predicates mean predictable SMT and little instability, because there are no quantifiers in VCs (reflection uses unfolding, not quantified axioms). That is a strong argument for designing ProofScript's SMT encoding to be quantifier-free where possible. The weaknesses:

- Error messages are poor ("Liquid Type Mismatch" with a huge constraint dump).
- Specs live outside GHC's type system, which creates impedance with type classes and GADTs.
- Maintenance couples tightly to GHC versions.
- Users sometimes struggle to tell when the lack of tactics means they need to restructure the proof instead.

### 7.2 RSC: Refinement Types for TypeScript

[Vekris, Cosman, Jhala, "Refinement Types for TypeScript", PLDI 2016](https://arxiv.org/abs/1604.02480) ([code: UCSD-PL/refscript](https://github.com/UCSD-PL/refscript)) is the closest prior art to the verification half of ProofScript. Key design points (from the paper):

- **Two-phase typing.** A first phase does ordinary (TS-like) typing and *elaborates* the program into a core calculus (FRSC/IRSC). The second phase adds refinements. Overloading and intersection types are resolved in phase one, so the refinement phase sees a monomorphic, explicit program. (This builds on [Vekris et al., "Trust, but Verify: Two-Phase Typing for Dynamic Languages", ECOOP 2015](https://arxiv.org/abs/1504.08039), where the "value-based overloading" common in JS, i.e. behaviour that depends on `typeof`, is handled by splitting into conjuncts and checking each against refinements.)
- **Mutability is tracked in types.** Each object type carries a mutability modifier: `Immutable`, `Mutable`, `ReadOnly`, `AssignsFields`, or `Unique`. The field-level distinction is between `immutable` fields (which may be referenced in refinements) and `mutable` fields (which may not). Refinements may only mention immutable fields and locals. This SSA-based approach avoids needing a heap logic: mutable locals become SSA variables, and refinements over mutable heap locations are simply disallowed. It sidesteps separation logic at the cost of expressiveness.
- **`this` and constructors.** Constructors type `this` with `AssignsFields`, which permits field initialisation, including immutable fields, until the constructor exits. Class invariants are refinements on immutable fields. Methods declare the mutability they need for `this`.
- **Reflection over `typeof`/tags.** The logic has measures for `ttag(x)` (`typeof`), `instanceof`, and `hasProperty`/enumerable keys, so path conditions from `typeof x === "number"` flow into refinements. Today's TS narrowing (discriminated unions, `in`) reconstructs exactly this.
- **Arrays.** `len` is a measure, and array bounds checks are the main case study.
- **Results.** Applied to parts of Octane, D3, the TypeScript compiler, and Transducers, RSC verified array bounds and other safety properties with modest annotation overhead. Most annotations were about mutability. It did not attempt full functional correctness or theorem proving.

**Status and lesson.** RefScript was a TS 1.x-era research prototype and was abandoned as TS evolved rapidly. That is the core risk for any TS-superset tool: **TypeScript is a moving target**, so ProofScript must depend on `tsc`/the TS API (or a stable subset) rather than reimplementing TS typing. Its key ideas still hold up: two-phase "TS types first, refinements second", mutability modifiers, and refining only over immutable data.

### 7.3 Flux (Rust)

[Lehmann et al., "Flux: Liquid Types for Rust", PLDI 2023](https://arxiv.org/abs/2207.04034). Flux layers liquid refinement types (indexed types like `RVec<i32>[n]` plus existentials) onto Rust and uses Rust's ownership to make *mutable* references refinable. Strong updates are allowed through `&strg` references. Because ownership guarantees no aliasing, refinements on mutable state become sound. Inference uses Horn clauses (liquid fixpoint). Compared with Prusti, Flux has much lower annotation overhead and verifies faster on equivalent programs. The lesson for TS: without an ownership discipline, refinements over mutable heap state are fundamentally hard in JS. RSC's immutable-only restriction, or a `readonly`/`unique` discipline, are the realistic options.

## 8. Rust verifiers

### 8.1 Verus

[Lattuada et al., "Verus: Verifying Rust Programs using Linear Ghost Types", OOPSLA 2023](https://arxiv.org/abs/2303.05491); [Lattuada et al., "Verus: A Practical Foundation for Systems Verification", SOSP 2024](https://dl.acm.org/doi/10.1145/3694715.3695952); [Verus guide: modes](https://verus-lang.github.io/verus/guide/modes.html).

**Modes.** Every function and variable has one of three modes:

| Mode | Purpose | Can call | Erased? | Checked how |
|---|---|---|---|---|
| `spec` | Mathematical definitions used in specs. Pure, total (decreases), uses `int`/`nat`/`Seq`/`Map`/`Set` | spec only | yes | definitions are encoded to SMT |
| `proof` | Lemmas. Ghost code whose body is a proof; may call spec and proof | spec, proof | yes | VC + SMT |
| `exec` | Real Rust code | all (proof via `proof { }` blocks) | no | VC + SMT, then rustc |

Ghost values cannot flow into exec values (mode checking is an information-flow check). `Ghost<T>` and `Tracked<T>` wrap ghost state in exec signatures and compile to zero-sized `PhantomData`. **Tracked** ghost variables obey Rust's linearity and borrowing. This "linear ghost types" design lets permission tokens such as `PointsTo<T>` encode separation-logic-style ownership of raw pointers and concurrent state *without a separation logic in the verifier*: Rust's borrow checker checks the ghost permissions. VerusSync generates tokenised concurrent protocols.

**Proofs.** SMT auto-active (Z3), with Dafny-like assertions, `by(nonlinear_arith)`, `by(bit_vector)`, `by(compute)`, and `assert forall ... by { }`. Verus carefully controls the SMT context: per-module pruning, `opaque`/`reveal`, `broadcast` lemmas, and spec function fuel. The goal is fast, stable verification, and the SOSP paper reports it verifying much faster than Dafny/F*-style tools on comparable benchmarks.

**Adoption.** Verified systems include Atmosphere (verified kernel), Anvil (Kubernetes controllers, OSDI 2024 best paper), a verified storage system (OSDI 2024 best paper), VeriSMo, Microsoft's verified page table and memory allocator work, and the [Asterinas](https://github.com/asterinas/asterinas) OS. Verus has a large and growing community.

**Lesson.** Verus's mode system is the cleanest way to put spec, proof, and executable code in the *same source language* with a clear erasure rule. Its weak point is that `spec` code is a separate sublanguage from exec code: `spec fn` uses `int` and `Seq`, while exec uses `u64` and `Vec`. Users must write and connect two versions (`view()` / `@`). The real lesson is to *minimise that gap*, ideally by letting pure exec functions be reflected into spec automatically. This is partly done via `#[verifier::when_used_as_spec]` and `pure` exec functions.

### 8.2 Creusot

[Denis, Jourdan, Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022](https://hal.inria.fr/hal-03737878). Creusot translates Rust MIR into Why3 (Coma IR). It handles mutable borrows with **prophecies** (the final value of a mutable borrow `^x`, from [Matsushita et al., "RustHorn", ESOP 2020/TOPLAS 2021](https://dl.acm.org/doi/10.1145/3462205)), which gives a purely functional logic for `&mut`. Specs (`#[requires]`, `#[ensures]`, `#[logic]`, `#[ghost]`) are written in Pearlite, a Rust-like logic. Why3 dispatches to multiple solvers (Z3, CVC5, Alt-Ergo), and Coq handles hard goals. The lesson: prophecies are elegant for borrows but need ownership. For JS, the analogous idea is "unique" references.

### 8.3 Prusti

[Astrauskas et al., "Leveraging Rust Types for Modular Specification and Verification", OOPSLA 2019](https://dl.acm.org/doi/10.1145/3360573). Built on the Viper permission-based infrastructure (implicit dynamic frames). Prusti derives separation-logic footprints from Rust types automatically, so users write only functional specs. Pure functions (`#[pure]`) can appear in specs, an early form of "exec functions reflected into spec". Development has slowed relative to Verus. Lessons: automatic footprint generation is good UX, while the Viper and Silicon/Carbon stack is a large TCB and slow.

### 8.4 Aeneas

[Ho & Protzenko, "Aeneas: Rust Verification by Functional Translation", ICFP 2022](https://arxiv.org/abs/2206.07185); [Ho, Fromherz, Protzenko, "Sound Borrow-Checking for Rust via Symbolic Semantics", ICFP 2024](https://arxiv.org/abs/2404.02680); [lean-lang.org/use-cases/aeneas](https://lean-lang.org/use-cases/aeneas). Aeneas translates safe Rust via Charon (MIR extraction) and a symbolic execution over the LLBC borrow calculus into **pure functional code in Lean** (also F*, Coq/Rocq, HOL4). Each function that returns a mutable borrow becomes a forward function plus *backward functions* that compute the updated values. Proofs are then done in Lean, often with `progress`, `scalar_tac`, and `simp`. It handles loops (as recursive functions), arithmetic overflow (as `Result`), and panics. Microsoft uses it to verify SymCrypt components ported to Rust.

**Lesson.** "Translate the executable language into the prover's pure language, then prove in the prover" works well when the source language's aliasing discipline (Rust ownership) makes a functional model possible. For TS, the same approach (as Thales and LemmaScript do) requires restricting to a mutation-free or ownership-checkable subset. It also creates a gap between the code the user writes and the model being proven: the translation is trusted.

## 9. Other systems (briefly)

- **Why3** ([why3.lri.fr](https://www.why3.org); [Filliâtre & Paskevich, "Why3 — Where Programs Meet Provers", ESOP 2013](https://hal.inria.fr/hal-00789533)): WhyML plus a multi-prover platform. VCs are split and sent to many SMT/ATP solvers and to Coq/Isabelle, with proof sessions recording which prover proved what. *Lesson:* a portfolio of solvers plus saved proof sessions mitigates single-solver brittleness. Ghost code and regions (alias control) are first-class. Also a back end for Creusot, SPARK, and Frama-C.
- **Stainless** (Scala; [Hamza, Voirol, Kunčak, "System FR", OOPSLA 2019](https://dl.acm.org/doi/10.1145/3360592)): verifies a pure-functional Scala subset (plus some imperative features, eliminated by AntiAliasing/ImperativeCodeElimination) via Inox and SMT. Specs are `require`/`ensuring`, and *lemmas are ordinary Scala functions returning `Unit` with `ensuring`*, a direct analogue to what ProofScript would do in TS. The host compiler (scalac) compiles the code, and Stainless's annotations are library calls. Incremental adoption was demonstrated in industry (Euler's SmartContracts, ETH). *Lesson:* "specs as ordinary library calls in the host language" (`require(...)`, `.ensuring(res => ...)`) needs no syntax extension at all.
- **SPARK/Ada** ([AdaCore SPARK](https://www.adacore.com/about-spark)): Ada subset plus contracts (`Pre`, `Post`, `Loop_Invariant`, `Ghost` aspect), proved via GNATprove → Why3 → SMT. Ownership-based pointer handling has been in place since 2019. Graded "levels" (Stone: valid SPARK subset; Bronze: data/flow; Silver: absence of runtime errors; Gold: key properties; Platinum: full functional correctness) form an explicit **incremental adoption ladder**, with NVIDIA's adoption a much-cited success. *Lesson to copy directly:* define adoption levels for ProofScript.
- **Whiley** ([whiley.org](https://whiley.org); Pearce): an imperative language with refinement-like types and VC verification. It compiled to JS at one point. Shows that a small team can't sustain a whole new language plus a verifier, which argues for piggybacking on TS.
- **ATS** (Xi): dependent types plus linear types over ML-like code, with proofs as erased terms ("programming with theorem proving"). It compiles to C. Very powerful, very hard to use. *Lesson:* expressiveness without ergonomics fails.
- **Cogent** ([O'Connor et al., ICFP 2016](https://dl.acm.org/doi/10.1145/2951913.2951940)): a linear, purely functional language compiling to C with *certifying compilation*: it produces an Isabelle proof that the C refines the functional semantics. *Lesson:* translation validation is an alternative to trusting the compiler.
- **Granule** ([Orchard, Liepelt, Eades, ICFP 2019](https://dl.acm.org/doi/10.1145/3341714)): graded modal types generalising QTT-style quantities (security levels, usage counts) as an SMT-checked index. It shows quantities can generalise beyond {0,1,ω}.
- **Koka** ([Leijen, "Koka: Programming with Row Polymorphic Effect Types", 2014](https://arxiv.org/abs/1406.2061)): row-polymorphic effect types (`total`, `div`, `exn`, `st<h>`, `io`) with effect inference, plus Perceus reference counting with reuse ([Reinking et al., PLDI 2021](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)). **Compiles to JS** (and C). Koka shows that inferred effect rows such as `total`/`div`/`exn` are lightweight enough for mainstream-feeling code. That is a strong model for ProofScript to *infer* whether a TS function is total/pure (and thus reflectable into logic) instead of making users annotate it.
- **CakeML** ([Kumar et al., POPL 2014](https://cakeml.org)): an ML dialect with a verified compiler in HOL4 and *proof-producing translation* from HOL functions to CakeML. The gold standard for an end-to-end TCB, but out of reach for a JS target (JS engines are not verified).
- **Nagini** (Python; [Eilers & Müller, CAV 2018](https://link.springer.com/chapter/10.1007/978-3-319-96145-3_33)): verifies statically typed (mypy-annotated) Python via Viper, with specs as library calls (`Requires(...)`, `Ensures(...)`, `Acc(...)`). Precedent for "use the gradual type checker's types as the base layer and specs as calls" in a dynamic language.
- **esverify** ([github.com/levjj/esverify](https://github.com/levjj/esverify); Schuster's [UCSC dissertation](https://escholarship.org/content/qt6x85w65n/qt6x85w65n.pdf)): verifies a JS subset (immutable objects and arrays, simple immutable classes, no inheritance) with specs as pseudo-calls `requires(...)`/`ensures(...)` and Z3. Higher-order specs use `spec(f, pre, post)`. Notable for a *live-programming* IDE with counterexample-driven test generation and step-through of failing VCs. A research prototype. *Lesson:* showing concrete counterexamples is the best error-message UX for SMT failures.
- **JaVerT / JaVerT 2.0 / Gillian** ([Fragoso Santos et al., POPL 2018](https://dl.acm.org/doi/10.1145/3158138); [Gillian, PLDI 2020](https://dl.acm.org/doi/10.1145/3385412.3386014)): separation-logic symbolic execution for full ES5 strict, compiled to the JSIL intermediate language, with a trusted-but-tested compiler (validated against Test262). Gillian generalises this into a language-agnostic platform (JS, C, Rust). It handles prototypes, getters/setters, and dynamic property access. *Lesson:* precise JS semantics is enormously complex. Verifying "real JS" at the heap level requires separation logic and heavy annotations, and has seen little practical adoption.
- **KJS** ([Park, Stefănescu, Roşu, "KJS: A Complete Formal Semantics of JavaScript", PLDI 2015](https://dl.acm.org/doi/10.1145/2737924.2737991)): an executable ES5.1 semantics in K, passing all of Test262 core. **JSCert** ([Bodin et al., POPL 2014](https://dl.acm.org/doi/10.1145/2535838.2535876)): a Coq-mechanised ES5 semantics with JSRef, a reference interpreter extracted from Coq. *Lesson:* a faithful semantics of full JS exists, but it is large. ProofScript should verify a *well-behaved subset* and state its assumptions clearly, rather than modelling all of ECMAScript.
- **Recent TypeScript ↔ prover bridges (2025–26):**
  - [**LemmaScript**](https://github.com/midspiral/LemmaScript) (tech preview; [README](https://cdn.jsdelivr.net/npm/lemmascript@0.6.1/README.md)): ordinary TS with `//@ requires/ensures/invariant/decreases/type` comment annotations, translated to Dafny or Lean 4 (Velvet/Loom). Generated files sit beside user-written proof files, with a regeneration discipline: diffs must be additions only.
  - [**Thales**](https://github.com/jessealama/thales): a TS-to-Lean 4 compiler written in Lean. It accepts a strict, mutation-free, class-free subset and emits a Lean sidecar: `T | null` becomes `Option`, `@throws` becomes `Except`, `@total` is termination-checked, and non-total recursion becomes `partial def`. It relies on postulated IEEE-754 axioms.
  - **lean-agentic** (npm, promotional, unverified claims).

  These confirm demand, and they confirm the "translate TS to an existing prover" architecture as the low-cost path. Their limits are telling: no mutation, no classes, and proofs live in a *different* language from the code. That is exactly the gap ProofScript intends to close. No mature system offers dependent types *inside* TypeScript syntax with erasure to TS. (Older experiments encode type-level naturals and vectors with TS's conditional and template literal types, but TS's type system is unsound and has no proof terms, so they are not verification tools.)

## 10. AI-assisted proving: why it affects ProofScript's design

- **Theorem proving.** AlphaProof (DeepMind; IMO 2024 silver; full paper in *Nature*, 2025) uses RL over Lean. DeepSeek-Prover V1.5/V2 ([arXiv:2504.21801](https://arxiv.org/abs/2504.21801)) are open Lean provers that use subgoal decomposition. ByteDance [Seed-Prover](https://arxiv.org/abs/2507.23726) fully proved 5 of 6 IMO 2025 problems in Lean. Harmonic's [Aristotle](https://arxiv.org/abs/2510.01346) reported gold-equivalent formal IMO 2025 solutions. Lean Copilot ([Song, Yang, Anandkumar, 2024](https://arxiv.org/abs/2404.12534)) and LeanDojo ([Yang et al., NeurIPS 2023](https://arxiv.org/abs/2306.15626)) put LLM suggestions into the tactic loop.
- **Verified code generation.** The [vericoding benchmark](https://arxiv.org/abs/2509.22908) (Sept 2025; 12.5k specs) found off-the-shelf LLMs succeeded on **82% in Dafny, 44% in Verus, 27% in Lean**. Follow-ups such as AlgoVeri (ICML 2026) show the same ordering on aligned tasks. AutoVerus ([Yang et al., 2024](https://arxiv.org/abs/2409.13082)) and Clover/Laurel for Dafny (LLMs generating assertions and lemmas) show LLMs filling in the "auto-active glue".

**Design implications.**

1. A *kernel-checked* proof format makes LLM output safe to trust: LLMs can hallucinate, and a checker filters them out. Unsound escape hatches (`assume`, `{:axiom}`, `sorry`) must be loudly auditable, because LLMs will use them to "succeed". Benchmarks have had to police this.
2. Auto-active, SMT-backed styles (Dafny) are currently *easier* for LLMs than tactic proofs, because the model writes code-like assertions and the solver fills gaps. Lean's advantage is the training data volume for mathematics.
3. Machine-readable goal states, structured errors, and counterexamples, plus a fast incremental checker exposed as an API/LSP, are now first-class usability requirements. The "user" is often an agent.
4. Proof-maintenance costs fall if AI repairs broken proofs. That makes a richer, more expressive logic more affordable, but only if proofs are checkable deterministically. SMT instability is especially toxic for agents, since a proof that passes and then flakily fails confuses repair loops.

---

## 11. Synthesis

### 11.1 Comparison table

| System | Core logic | Proof style | Spec attachment | Exec ↔ logic | Partiality / non-termination | Mutation handling | TCB | Targets |
|---|---|---|---|---|---|---|---|---|
| Lean 4 | CIC + quotients, impredicative proof-irrelevant `Prop` | Tactics + terms; strong automation (simp, omega, grind, decide), kernel re-checks all | Dependent types / theorems | Same language; `Prop`/types erased; `partial`, `implemented_by`, `extern`, `noncomputable` | `partial` = opaque; WF recursion with proofs | Pure `do` desugaring; RC destructive update; `Std.Do` | Small kernel + 3 axioms; external checkers | C (native) |
| Idris 2 | QTT | Terms, holes, search | Dependent types | Multiplicity 0 = erased, *typed* erasure | Opt-in `total` | Linear types (q=1) | Checker (not minimal) | Chez, JS, C |
| Agda | MLTT (+ cubical) | Terms, holes | Types | `@0` erasure, `Prop` | Termination checker | — | Checker | Haskell, JS |
| Rocq | pCIC, Prop/Set/SProp | Ltac tactics + terms | Types | Extraction erases Prop (unverified; MetaCoq verified erasure) | Total only | Monads / Iris | Small kernel | OCaml, Haskell, Scheme, C (CertiCoq) |
| F* | Dependent types + refinements + effect lattice | SMT + lemma calls + Meta-F* tactics | Refinements, `requires/ensures` in effect indices | `GTot`/`erased` erased; Low* → C | `Div` effect, banned in specs | `ST` Dijkstra monads, HyperStack, Pulse | Typechecker + Z3 + extraction | OCaml, F#, C, (JS/Wasm) |
| Dafny | First-order-ish spec logic over imperative OO | Auto-active SMT | `requires/ensures/modifies/decreases` | `ghost` modifier, erased | `decreases`, `decreases *` | Dynamic frames, `modifies` | Dafny→Boogie→Z3 + compilers | C#, Java, **JS**, Go, Python, Rust |
| Liquid Haskell | Refinements in decidable SMT logic | Liquid inference + reflection/PLE; proofs as Haskell fns | `{-@ @-}` comments / plugin | `reflect`ed fns in logic; proofs run as unit fns | Termination by metrics, `lazy` | Pure language | LH + Z3 + GHC | GHC |
| RSC (TS) | Refinements on two-phase elaborated TS | Liquid inference | Annotations in TS | Refinements erased | — | Mutability modifiers; refine only immutable | RSC + Z3 | TS/JS |
| Verus | Rust + spec logic (int/Seq/Map) | Auto-active SMT, curated context | `requires/ensures` + modes | **spec/proof/exec modes**; Ghost/Tracked erased | `decreases` (spec/proof); exec may diverge | Rust ownership + linear ghost permissions | Verus + Z3 + rustc | Rust native |
| Creusot | Why3 logic, prophecies | SMT via Why3 + Coq | Attributes, Pearlite | `#[logic]`, `#[ghost]` erased | variant | Prophecies for `&mut` | Translation + Why3 + solvers | Rust |
| Aeneas | Prover's (Lean) | Lean tactics | Lean theorems about translated fns | Rust → pure Lean model | Lean `Result` + fuel/partial | Backward functions | Translation + Lean kernel | Rust (unchanged) |
| Stainless | System FR | SMT, lemma fns | `require/ensuring` library calls | Ghost annotations | Measures | Imperative elimination | Stainless + SMT | Scala |
| SPARK | Ada subset + contracts | SMT via Why3 | Ada aspects | `Ghost` aspect | Loop variants | Ownership | GNATprove + solvers | Ada native |
| esverify / LemmaScript / Thales | TS/JS subset → Z3 / Dafny / Lean | SMT / Dafny / Lean tactics | `requires()` calls / `//@` comments / JSDoc tags | Translation to separate prover | `@total`, `decreases` | Immutable subset only | Translator + backend | Original TS unchanged |

### 11.2 Patterns that recur and work

1. **A mode or sort system that separates spec, proof, and exec code, with typed erasure.** This appears as Verus spec/proof/exec, Dafny ghost, F* `GTot`/`erased`, Idris quantity 0, Coq/Lean `Prop`, and Agda `@0`. All of them check *statically* that erased things can't influence runtime values, so erasure is sound by construction. Idris/QTT does it per binder, Verus per function and variable, and Dafny per declaration. *For ProofScript:* every binder has a mode (`erased`/ghost vs. runtime), with sensible inference: types, `Prop`-valued arguments, and theorem functions are erased by default.

2. **A pure, total logical fragment, separate from effectful executable code.** Logic must only see total, deterministic functions. The fragment is enforced through F*'s `Tot` vs. `Div`, Verus's spec vs. exec, Dafny's `function` vs. `method`, Lean's opaque `partial`, and Koka's `total` effect. Non-termination and effects are allowed in executable code but can't leak into types.

3. **Reflection of executable functions into the logic.** Liquid Haskell's `reflect`, Dafny 4 compiled `function`s, Verus's `when_used_as_spec`, Prusti's `#[pure]`, and Lean's "the program *is* the definition". When the same function is both executed and reasoned about, specs don't diverge from code. This is the main way to avoid the "two languages" problem.

4. **Proofs are ordinary functions in the host language.** F* `Lemma`, Dafny `lemma`, Liquid Haskell `Proof`, Stainless `ensuring`-returning-`Unit`, and Verus `proof fn`. Induction is recursion, case analysis is `switch`/`match`, and applying a lemma is a function call. This is the most promising user model for "theorems in TS syntax": `function plusComm(a: nat, b: nat): Proof<Eq<a+b, b+a>>`.

5. **A small trusted kernel with untrusted elaboration and automation.** Lean (kernel plus external checkers), Coq/Rocq, and HOL-family systems. Any automation, including SMT, tactics, and LLMs, is safe if it produces a checkable certificate. This is the right long-term TCB story, and AI makes it more valuable.

6. **SMT for decidable side conditions, kept quantifier-free where possible.** Liquid types restrict refinements to decidable theories and use unfolding (PLE) rather than quantified axioms, and stay predictable. Lean's `omega`/`grind`/`decide` show that you can get SMT-like automation *with* proof terms. Linear arithmetic, bounds, and nullability make up the bulk of program-verification VCs.

7. **Two-phase elaboration onto the host type system.** RSC types the program with the host's ordinary type discipline first, then layers refinements and dependent types on the elaborated core. Imperative `do`-notation can similarly be desugared to a pure core (Lean's `do Unchained`), and Aeneas/Creusot model borrows functionally. For ProofScript: reuse `tsc` for ordinary TS typing, then elaborate a *core* calculus where dependent types and proofs live.

8. **Graded or incremental adoption.** SPARK's Stone→Platinum levels, Liquid Haskell/Nagini/Stainless specs in comments or library calls with the host compiler unchanged, Dafny `{:verify false}`, Lean's `sorry` with axiom tracking, and gradual verification ([Bader, Aldrich, Tanter, "Gradual Program Verification", VMCAI 2018](https://arxiv.org/abs/1711.03608)). Unverified code coexists with verified code at module boundaries, and assumptions are tracked and auditable (`#print axioms`, `dafny audit`).

9. **Mutation handled by ownership or immutability, not by modelling the full heap.** Flux, Verus, Aeneas, Creusot, and Prusti all exploit Rust ownership, while RSC restricts refinements to immutable data. Full-heap JS verification (JaVerT/Gillian) is heavy and unadopted.

10. **Pure code compiled to efficient mutation.** Lean's and Koka's reference counting with reuse lets users write pure code that compiles to in-place updates. Relevant if ProofScript's logical fragment is pure but must run efficiently in JS (less applicable, since JS has a GC; a uniqueness analysis could still emit in-place array updates).

### 11.3 Failure modes and pitfalls

1. **SMT brittleness and instability.** Mariposa ([Zhou et al., FMCAD 2023](https://github.com/secure-foundations/mariposa)) measured instability across thousands of Dafny and F* queries. A follow-up study (Dafny, F*, Verus) found most unstable queries trace to quantifier instantiation, and 87% of the repairable ones involve a single quantifier. Seeds, Z3 version bumps, renamings, or irrelevant context flip results. Mitigations: minimise quantifiers, prune context (Verus), make definitions `opaque` by default, solver portfolios (Why3), and cache or record proof certificates. Brittleness is a top driver of AWS Cedar's move from Dafny to Lean.
2. **Unsound axioms and escape hatches.** `assume`, `{:axiom}`, `believe_me`, `sorry`, `implemented_by` mismatches, `native_decide`, and `extern` specs. Thales already relies on 12 postulated IEEE-754 axioms. Pitfall: unsafety that is silent or transitively invisible. Mitigation: every escape hatch is tracked transitively (`#print axioms`-style) and reported in CI.
3. **Extraction and translation gaps.** Coq extraction is unverified, Dafny's compilers have bugs (ISSTA 2022), and translation tools (Aeneas, LemmaScript, Thales) prove the *model*, not the code. For JS: `number` is IEEE-754, not ℤ; `===` vs. `Object.is`; `-0` and `NaN`; property-order semantics; getters with side effects; prototype pollution; `any` crossing the boundary; mutation via aliases from unverified code. A proof about the model is only as good as the faithfulness of the translation.
4. **The spec language diverging from the implementation language.** Verus has `spec` `int`/`Seq` vs. exec `u64`/`Vec`. Liquid Haskell's spec language has a different syntax from Haskell. Creusot has Pearlite, and Dafny has `seq` vs. arrays. Users duplicate logic and write abstraction functions. Mitigation: one language, with reflection of total pure functions.
5. **Proof maintenance costs.** Mathlib refactors, Coq version upgrades, F* proofs breaking with Z3 upgrades, and SMT proofs that time out after an unrelated edit. Explicit, structured proofs (Lean `calc`, Dafny `calc`) and stable automation are more maintainable than sprawling tactic scripts or giant SMT queries. Deterministic checking plus AI repair helps.
6. **The host language moves out from under you.** RefScript died with TS 1.x. Liquid Haskell constantly chases GHC. Any TS superset must track a fast-moving TS (and the Go-native `tsgo` compiler, TypeScript 7). Mitigation: don't fork TS typing. Use the official compiler API/LSP for the base type layer, and keep the ProofScript extension surface narrow and syntactically stable.
7. **Unsoundness in the base type system.** TS's type system is deliberately unsound: bivariant method parameters, `any`, unchecked casts, `!`, index signatures without `noUncheckedIndexedAccess`, and covariant arrays. A verifier that *trusts* TS types inherits these holes. RSC addressed this by re-checking in its own core. ProofScript must treat TS types as *hints* and re-verify them in its own sound core, or explicitly mark the boundary.
8. **Poor error UX.** "Could not prove postcondition" (Dafny/F*), Liquid Haskell's constraint dumps, and Lean unification failures. What works better: counterexamples (esverify, Dafny `--extract-counterexample`), goal views (Lean infoview), and hole-driven development (Agda/Idris).
9. **Performance of proof checking** in the edit loop. Verification must be incremental and cached per declaration (Lean's `.olean`, Verus's module-level checking, Dafny's verification cache) or the IDE becomes unusable.
10. **Expressiveness without ergonomics** (ATS, early Idris) → no adoption. **Ergonomics without a credible soundness story** → no trust.

### 11.4 Recommendation sketch for ProofScript

**Thesis:** combine **Lean's foundations and trust story** with **Verus/Dafny-style modes and auto-active specs**, using **Idris/QTT-style typed erasure** and **Liquid Haskell-style reflection** so the *same* TS functions are both executable and reasoned about. Reuse `tsc` for the TypeScript layer (the two-phase approach from RSC).

1. **Core logic.** A dependent type theory in the CIC/Lean family: a proof-irrelevant `Prop`, inductive types, quotients optional, and a minimal set of axioms (`propext`, `funext`, `choice` optional and tracked). Define a small core calculus, and implement the **kernel** as a small, separately auditable checker (in TS/Rust). Plan for an *independent* second checker, and possibly a mode that exports to Lean so Lean's kernel and lean4lean can double-check ProofScript proofs. Exporting to Lean also gives access to Lean's AI tooling and possibly Mathlib-style libraries.

2. **Modes and erasure (Verus × QTT).** Three modes: `spec` (pure, total, logic-visible, erased), `proof` (theorems and lemmas, erased, total), and `exec` (ordinary TS, emitted). Binders inside exec code may be erased (`ghost`/quantity 0). The type checker guarantees ghost values never flow into exec values, so erasure is a syntactic strip that leaves **plain, idiomatic TypeScript** with ghost parameters, proofs, and dependent indices removed. Default modes are inferred, the way Idris infers quantity 0 for type-level arguments: anything returning `Proof<...>`/`Prop` is `proof`.

3. **One language, reflection instead of duplicate spec languages (Liquid Haskell, Dafny 4).** Any exec function that ProofScript can show to be **pure, total, and deterministic** is automatically reflected into the logic: an effect inference in the style of Koka's `total`/`div`/`exn` over a TS subset, with no I/O, no mutation of non-local state, structural or `decreases` termination, and no `any`. Such a function can be used directly in types and theorems, so users never write the logic twice. Functions outside that fragment remain opaque to the logic (Lean's `partial` model): callable from exec, and specifiable with contracts, but not unfoldable.

4. **Proofs are TS functions, with tactics as an escape hatch.** Theorems are function signatures returning `Proof<P>` (or `P` in `Prop`), and proofs are function bodies: `switch` on inductives for case analysis, recursion for induction, calls for lemma application, and a `calc`-style chain helper for equational reasoning. Provide `by(...)` blocks that run *tactics written in TS/ProofScript* (Lean-style metaprogramming in the host language), including `simp`, `omega`/`grind`-like decision procedures, and `decide`. All tactics and SMT must emit **kernel-checkable proof terms or certificates**. Where we temporarily trust an SMT solver, mark it as a tracked axiom, as F* and Dafny should have.

5. **Auto-active contracts for ordinary TS (Dafny/Verus/RSC).** `requires`/`ensures`/`invariant`/`decreases` on exec functions, in TS syntax. Ideally refinement types (`number & { v | v >= 0 }`) via a syntax that degrades to plain TS. VCs go first to quantifier-free decision procedures (linear arithmetic, arrays/length, tags, nullability, all certificate-producing), then to SMT, then to the user/LLM. Avoid quantified axioms in the default encoding (Liquid/PLE lesson) to dodge Mariposa-style instability.

6. **JS semantics: honest, layered models.** Model `number` as IEEE-754 doubles, and provide a separate `int`/`nat` (logic, or `bigint` at runtime) and bounded-integer refinements (`safeInt`) so arithmetic proofs are about real JS behaviour. Handle mutation RSC-style first: refinements and reflection over `readonly`/immutable data and local mutable variables (SSA/`do`-unchained desugaring). Later, consider a `unique`/ownership discipline (Flux/Verus) or a separation-logic layer for heap-mutating code. Don't attempt full ECMAScript (JaVerT/KJS show the cost). State the trusted assumptions: the verified subset, the JS engine, and the boundary with unverified code.

7. **Gradual adoption, SPARK-style levels.** Levels from "checks under ProofScript with no specs" through absence of runtime errors (no `undefined` access, bounds, no throws), to contracts, to full functional correctness. Unverified TS modules interoperate, and contracts at the boundary can be compiled to runtime checks (gradual verification; [Racket-style contracts](https://docs.racket-lang.org/guide/contracts.html)) when unverified callers enter verified code. `sorry`/`assume`/`trusted` are tracked transitively and surfaced by `proofscript audit`.

8. **Tooling built for humans and agents.** An LSP with goal display, holes, counterexamples, and machine-readable goals. Deterministic, incremental, per-declaration cached checking. An LLM-friendly surface (TS syntax is in every model's training data) with mandatory kernel checking. This gives ProofScript a plausible edge: the vericoding data says LLMs are better at code-like auto-active proofs than at Lean tactics, and TS is the most familiar syntax to LLMs.

9. **What not to borrow.** Don't make SMT the TCB, which is the F*/Dafny approach. Don't build a separate spec sublanguage (Verus `spec` types, Pearlite). Don't fork the TS type checker (RefScript). Don't extract to unidiomatic output that requires a heavy runtime (Dafny JS). Don't let `partial`/`implemented_by`-style hatches be silent.

**Short version:** Lean's kernel plus Verus's modes plus Idris's typed erasure plus Liquid Haskell's reflection plus Dafny's auto-active contracts, layered onto `tsc` through RSC-style two-phase elaboration, with SPARK-style adoption levels.

---

## References (selected, in addition to inline links)

- Lean 4: https://lean-lang.org ; reference manual https://lean-lang.org/doc/reference/latest/ ; lean4lean https://arxiv.org/abs/2403.14064
- Idris 2: https://arxiv.org/abs/2104.00480 ; QTT https://bentnib.org/quantitative-type-theory.pdf
- F*: https://fstar-lang.org ; Proof-oriented Programming in F* https://fstar-lang.org/tutorial/
- Dafny: https://dafny.org ; https://github.com/dafny-lang/dafny
- Liquid Haskell: https://ucsd-progsys.github.io/liquidhaskell/ ; Refinement Reflection https://arxiv.org/abs/1711.03842
- RSC: https://arxiv.org/abs/1604.02480 ; https://github.com/UCSD-PL/refscript
- Verus: https://verus-lang.github.io/verus/guide/ ; https://arxiv.org/abs/2303.05491
- Creusot: https://github.com/creusot-rs/creusot ; Prusti: https://github.com/viperproject/prusti-dev ; Aeneas: https://github.com/AeneasVerif/aeneas ; Flux: https://flux-rs.github.io/flux/
- Mariposa: https://github.com/secure-foundations/mariposa
- Vericoding benchmark: https://arxiv.org/abs/2509.22908
- LemmaScript: https://github.com/midspiral/LemmaScript ; Thales: https://github.com/jessealama/thales ; esverify: https://github.com/levjj/esverify
- Gillian: https://gillianplatform.github.io ; KJS: https://github.com/kframework/javascript-semantics ; JSCert: https://github.com/jscert/jscert
