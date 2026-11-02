# ProofScript Hard Requirements

Status: **design draft v0.1** (2026-11-02). Derived from [research/01](../research/01-typescript-success-principles.md) (why TypeScript won) and [research/03](../research/03-foundations-and-soundness.md) (what soundness demands).

TypeScript won because adopting it was nearly free and leaving it was nearly free: every JavaScript program was (practically) already a TypeScript program, types vanished at emit, and you paid for exactly as much checking as you asked for. ProofScript must have the same relationship to TypeScript. On top of that it adds one property TypeScript explicitly gave up: **what ProofScript says is proved must actually be true.**

These requirements are binding. A feature that violates one is redesigned or dropped.

## A. Superset requirements (the TS ⊂ ProofScript relationship)

| # | Requirement | TypeScript analogue |
|---|---|---|
| **R1** | **Every valid TypeScript file is a valid ProofScript file with identical meaning and identical emit.** Renaming `foo.ts` → `foo.pts` never changes runtime behaviour and never introduces new errors. | Renaming `.js` → `.ts` keeps behaviour (Design Goal 7: "preserve runtime behavior of all JavaScript code"). |
| **R2** | **No reinterpretation.** No token sequence that is valid TypeScript may be given a different meaning in ProofScript. New keywords are contextual and are only recognized in positions where the same tokens would be a TypeScript syntax error (see [design §7.1](02-language-design.md#71-the-no-reinterpretation-rule)). | `satisfies`, `asserts x is T`, `accessor`, `using` were all added this way. |
| **R3** | **Erasure: compile = strip.** All ProofScript-specific syntax is removed by a purely syntactic, single-file, checker-free pass that turns `.pts` into TypeScript that stock TS tools parse, and whose JavaScript emit is exactly the program's runtime meaning. The pass replaces erased text with whitespace, so line and column positions never change. (A separate, semantic *declaration view* produces fully type-valid TS for `tsc`, `.d.ts` emit and `proofscript eject`; see [design §10](02-language-design.md#10-tooling-architecture).) | `isolatedModules`, `--erasableSyntaxOnly`, Node type stripping, `ts-blank-space`. |
| **R4** | **Proofs never affect runtime.** The JavaScript produced from a ProofScript file never depends on whether, or how, its proofs check. No proof, spec, ghost value, or theorem has a runtime footprint. ProofScript never inserts runtime checks; any runtime check is code the user wrote. | Non-goal 5: never "emit different code based on the results of the type system". Goal 3: no runtime overhead. |
| **R5** | **Proof failures don't block emit by default.** Like type errors, they are diagnostics; `noEmitOnProofError` is opt-in. | Type errors don't block emit. |
| **R6** | **No runtime dependency.** Compiled output imports nothing from ProofScript. | TS emits no runtime library (`tslib` is optional, for downlevelling only). |
| **R7** | **Bidirectional interop.** `.pts` modules import and are imported by `.ts`, `.tsx`, `.js` and `.d.ts` modules, through the normal module system. A `.pts` module exposes ordinary `.d.ts` declarations to TS consumers, plus `.d.pts` specs to ProofScript consumers. | `.ts` ↔ `.js` interop; `.d.ts` files. |
| **R8** | **Works inside the existing toolchain.** ProofScript integrates with `tsc`/TS 7, editors, Node, Vite, esbuild, Bun, Deno and bundlers. It never asks a project to replace them. | TS slotted into existing JS build pipelines. |
| **R9** | **Track TypeScript and ECMAScript.** New TS and TC39 syntax becomes valid ProofScript as it ships. ProofScript's own syntax stays bracket-balanced and keyword-led so it remains robust to the TC39 type-annotations proposal. | Goal 6: align with current and future ECMAScript proposals. |

## B. Incremental adoption requirements

| # | Requirement | TypeScript analogue |
|---|---|---|
| **R10** | **Pay only for what you ask for.** A `.pts` file with no specs costs nothing beyond TypeScript checking and produces no new errors. Verification obligations arise only from specs the user wrote (`requires`, `ensures`, `theorem`, refinement types, ...) and from the code those specs depend on. | Untyped JS in a `.ts` file mostly just works; `strict` is opt-in. |
| **R11** | **Granular opt-in.** Verification can be adopted per project, per file (rename to `.pts`), per declaration (add a spec) and per obligation (`admit`). | `allowJs`, `checkJs`, `@ts-check`, `@ts-expect-error`, `any`. |
| **R12** | **Graduated assurance levels**, from "TS with specs as documentation" to "fully verified, no assumptions", selectable per module and enforceable in CI ([design §9](02-language-design.md#9-assurance-levels-and-adoption)). | `strict` flag family. SPARK's Stone→Platinum levels. |
| **R13** | **Specs for code you don't own.** Third-party JS/TS can be given specifications in `.d.pts` sidecar files without modifying or re-verifying it. Those specs are assumptions and are tracked as such (R16). | `.d.ts` files and DefinitelyTyped. |
| **R14** | **Tooling is the product.** Proof checking runs in the editor, incrementally, with hover, go-to-definition, rename across code and specs, and a live goal/proof-state view. CI gating is one command. | Goal: tooling-first; tsserver. |

## C. Soundness requirements (where ProofScript deliberately differs from TypeScript)

TypeScript's non-goal 3 is "apply a sound or provably correct type system". ProofScript keeps TypeScript's type system exactly as it is, and adds a separate layer for which soundness *is* the goal.

| # | Requirement |
|---|---|
| **R15** | **Proofs are sound.** Every theorem and every verified spec is checked by a small, independent **kernel** for a well-understood logic (Lean 4's type theory). Everything else (parser, elaborator, tactics, SMT solvers, decision procedures, `tsc`) is untrusted: its output must be re-checked by the kernel, or recorded as an explicit assumption. Proofs are exportable so independent checkers (e.g. Lean's own kernel) can re-check them. |
| **R16** | **Every assumption is explicit and auditable.** `assume`, `admit`, `.d.pts` specs of unverified code, solver results not yet certified, and environment assumptions are all recorded in each theorem's **trust footprint**. `proofscript audit` prints it. "Verified" means the footprint contains only the standard axioms and the documented environment assumptions. |
| **R17** | **TypeScript types are never trusted by proofs.** TS's checker keeps running and keeps doing what it does, but its judgements (and `any`, `as`, bivariance, `.d.ts` declarations) contribute nothing to what a proof may assume. Facts about values from unverified code come only from verified validators, verified runtime checks, or tracked assumptions. |
| **R18** | **ProofScript never weakens TypeScript.** It does not suppress, relax or replace any TS diagnostic. |
| **R19** | **Honest JavaScript semantics.** The logic models what JS actually does: `number` is IEEE-754 binary64 (with NaN, ±0, ±∞), strings are UTF-16 code units, `bigint` is an unbounded integer, objects have identity, functions may throw or not terminate. Integer and mathematical reasoning is available through *refinements that are proved*, never by pretending `number` is ℤ. |
| **R20** | **Nothing but an explicit `axiom` can make `False` provable.** Unverified or non-terminating code never enters the logic as an equation; `assume` specs are restricted to forms that cannot make the logic itself inconsistent ([design §6.6](02-language-design.md#66-assumptions-and-consistency)). Raw `axiom` declarations exist for experts, are off by default, and are always reported. |

## D. Process requirements

| # | Requirement |
|---|---|
| **R21** | The meaning of every ProofScript construct is specified by its elaboration into the kernel, documented in this repository. |
| **R22** | ProofScript is a superset forever: language changes never break valid TS, and breaking changes to ProofScript-only syntax are rare, versioned and migration-tooled. |

## Known tensions, and how the design resolves them

1. **TS's success depends on unsoundness; proofs require soundness.** Resolved by two layers: the TS layer stays unsound and untouched (R1, R18); the proof layer is sound and trusts nothing from the TS layer (R15, R17). The cost is friction at the boundary, which assurance levels (R12) and validators make explicit.
2. **Dependent types vs. erasure.** Values that appear in types must be erasable. Resolved by ghost positions with a checked erasure discipline (design §5), and by putting value-level type indices where TS already erases things (generic parameter lists, annotations).
3. **"Avoid adding expression-level syntax" (TS Goal 8) vs. inline proofs.** ProofScript adds no new *runtime* expression syntax. Its new syntax is confined to erasable, keyword-led clauses, statements and declarations.
4. **The "Fire Triangle" of gradual dependent types** (Pédrot & Tabareau 2020; GCIC, 2022): a kernel cannot be simultaneously gradual, normalizing and conservative. Resolved by never letting `any` into the kernel: the kernel is a normal (non-gradual) type theory, and graduality lives at the program level (R10–R13).
5. **Node's type stripping does not accept ProofScript syntax.** `.pts` needs a strip step or a loader (`node --import proofscript/register`), just as `.ts` needed `tsc` before Node 22.
