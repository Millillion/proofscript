# 01 — Why TypeScript Succeeded, and What ProofScript Must Inherit

*Research note for ProofScript (a TypeScript superset adding dependent types, theorems and proofs). Compiled 2026-11-02. All claims are sourced; where a source was secondary or I could not verify a detail, it is flagged.*

---

## 0. Executive summary

TypeScript (TS) won not because it had the best type system, but because it made **the cost of trying it approximately zero and the cost of leaving it approximately zero**. Every mechanism that matters reduces to a few properties:

1. **JS in, JS out.** (Almost) every JS program is a TS program; TS output is the same program minus the types.
2. **Types never change runtime behaviour** ("fully erasable", "no runtime type information"), so the type checker is *advisory*: errors do not block emit by default.
3. **Adoption is per-file, per-line, per-flag**: `allowJs`, `checkJs`, `// @ts-check`, `// @ts-nocheck`, `// @ts-expect-error`, `any`, `.d.ts`, and an opt-in `strict` family.
4. **Unsoundness is a feature**: the type system was explicitly *not* designed to be sound, trading correctness for the ability to type real-world JS idioms.
5. **The product is the editor experience** (language service), and the ecosystem (DefinitelyTyped, `.d.ts`) is a first-class deliverable.
6. **Alignment with the host language's standards body** (TC39) and refusal to add expression-level syntax kept TS from forking JavaScript.

Over 2022–2026 these properties hardened into ecosystem *contracts*: Node.js, Deno, Bun, Bloomberg's `ts-blank-space`, swc/esbuild/oxc all assume "TS = JS + erasable annotations". TS responded with `--isolatedModules`, `--verbatimModuleSyntax`, `--isolatedDeclarations` and `--erasableSyntaxOnly`. Any TS superset that breaks "strip and run" or "single-file transpile" will be locked out of this tool ecosystem.

Competitors that were *not* supersets (CoffeeScript, Dart 1, Elm, PureScript, ReScript) or that **stopped** being supersets/erasable or stopped serving outside users (Flow, Hack after HHVM 4.0) lost. The verification-tool analogues tell the same story: tools that **embed in the host language and erase cleanly** (SPARK aspects + ghost code, Verus/Creusot/Prusti/Kani attributes, Liquid Haskell comments, JML/ACSL comments, Python PEP 484) are the ones with industrial uptake inside existing codebases; separate languages (Dafny, F*, Lean) get used for *new*, isolated, high-assurance components.

The central tension for ProofScript is that TS's success *depends* on unsoundness, but proofs are meaningless without soundness. The resolution must be a **trust boundary**: ProofScript should be sound *inside a verified fragment* and treat everything crossing from ordinary TS as an explicit, auditable assumption — mirroring SPARK's Stone→Platinum levels and Rust verifiers' "trusted/external" annotations.

---

## 1. TypeScript's official Design Goals and Non-goals

Source: TypeScript wiki, "TypeScript Design Goals" — https://github.com/microsoft/TypeScript/wiki/TypeScript-Design-Goals (fetched 2026-11-02; quotes are verbatim).

### Goals

| # | Goal (verbatim) | Relevance to ProofScript |
|---|---|---|
| G1 | "Statically identify constructs that are likely to be errors." | ProofScript upgrades "likely" to "provably absent" — but only where the user opts in. |
| G2 | "Provide a structuring mechanism for larger pieces of code." | Theorems/specs become a structuring mechanism (interfaces with laws). |
| G3 | "Impose no runtime overhead on emitted programs." | Proofs, ghost code, specs, and refinement predicates **must** have zero runtime cost. |
| G4 | "Emit clean, idiomatic, recognizable JavaScript code." | ProofScript should emit the *same* JS that tsc would emit for the stripped program. |
| G5 | "Produce a language that is composable and easy to reason about." | — |
| G6 | "Align with current and future ECMAScript proposals." | ProofScript must align with *TypeScript* and, transitively, TC39 — including the type-annotations proposal. |
| G7 | "Preserve runtime behavior of all JavaScript code." | Analogue: preserve runtime behaviour of all TS code. |
| G8 | "Avoid adding expression-level syntax." | Strong pressure: proof syntax should live in type/declaration positions or in clearly bounded erasable regions, not new expression operators. |
| G9 | "Use a consistent, fully erasable, structural type system." | Dependent types and proofs must be **fully erasable**; structural typing must be preserved for TS-level compatibility. |
| G10 | "Be a cross-platform development tool." | — |
| G11 | "Do not cause substantial breaking changes from TypeScript 1.0." | Analogue: do not break existing TS. |

### Non-goals

| # | Non-goal (verbatim, with the page's "Instead…") |
|---|---|
| N1 | "Exactly mimic the design of existing languages." Instead, "use the behavior of JavaScript and the intentions of program authors as a guide for what makes the most sense in the language." |
| N2 | "Aggressively optimize the runtime performance of programs." Instead, "emit idiomatic JavaScript code that plays well with the performance characteristics of runtime platforms." |
| N3 | "Apply a sound or 'provably correct' type system." Instead, "strike a balance between correctness and productivity." |
| N4 | "Provide an end-to-end build pipeline." Instead, "make the system extensible so that external tools can use the compiler for more complex build workflows." |
| N5 | "Add or rely on run-time type information in programs, or emit different code based on the results of the type system." Instead, "encourage programming patterns that do not require run-time metadata." |
| N6 | "Provide additional runtime functionality or libraries." Instead, "use TypeScript to describe existing libraries." |
| N7 | "Introduce behaviour that is likely to surprise users." Instead "have due consideration for patterns adopted by other commonly-used languages." |

**Key takeaways for ProofScript.**
- N5 ("emit different code based on the results of the type system") is the single most important constraint to inherit: *proof results must never influence emit*. This is what makes "errors don't block emit" and "strip types with a dumb tool" possible.
- N3 is the goal ProofScript *deliberately inverts* — but only locally (see §4 and §10).
- N6/N4: ProofScript should describe existing TS libraries (via spec-only declaration files, analogous to `.d.ts`), not ship a runtime, and should plug into existing build pipelines rather than replace them.
- Note that TS itself violated G3/G9/N5 early on (enums, namespaces, parameter properties, legacy decorators with `emitDecoratorMetadata`), and has spent 2019–2026 walking those back via flags (§2.4). ProofScript should not repeat the mistake.

---

## 2. The precise superset relationship and type erasure

### 2.1 "Every JS program is a TS program" — mostly, with caveats

**Syntactic superset (mostly).** TS's parser accepts JavaScript syntax; any `.js` file can be renamed `.ts` and will parse. But there are known edge cases where TS is **not** a strict syntactic superset, or parses identical text differently:

1. **Generic-call ambiguity.** In JS, `f < a > (b)` is two comparisons `(f < a) > b`. In a `.ts` file the parser treats `f<a>(b)` as a call with an explicit type argument. Exotic, but a genuine divergence (this is also why the TC39 type-annotations proposal *cannot* reuse `f<T>(x)` syntax — see §6).
2. **`<T>x` casts vs. JSX.** The angle-bracket assertion `<Foo>bar` is valid in `.ts` but "TypeScript disallows angle bracket type assertions in `.tsx` files" because it conflicts with JSX; `as` must be used instead (https://www.typescriptlang.org/docs/handbook/jsx.html). Similarly a generic arrow `<T>(x: T) => x` in `.tsx` must be written `<T,>(x: T) => x`. Consequence: **file extension determines grammar** (`.ts`, `.tsx`, `.mts`, `.cts`, `.js`, `.jsx`, `.d.ts`).
3. **Contextual keywords** (`type`, `declare`, `abstract`, `namespace`, `module`, `satisfies`, `as`, `asserts`, `infer`, `keyof`, `readonly`, `is`, `out`/`in` variance annotations, `accessor`, `using`) are carefully contextual so that existing JS identifiers with those names still parse. ProofScript keywords (`theorem`, `proof`, `lemma`, `requires`, `ensures`, `invariant`, `ghost`, …) must be contextual in the same way.
4. **Semantic divergences that TS has historically emitted.** E.g. class-field semantics: older TS emitted constructor *assignments* where ES2022 uses `[[Define]]` semantics, controlled by `useDefineForClassFields` (now default-on for modern targets). TS 7.0 also turns `alwaysStrict: false` into a hard error (https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/), i.e. TS output is always strict-mode code. These are reminders that "superset" is a *goal maintained by constant care*, not an automatic property.

**Type errors do not block emit.** By default `tsc` emits JavaScript even when the program has type errors; `--noEmitOnError` is opt-in. This is fundamental: a JS program that "fails to type-check" as TS is still a *working* TS program that produces the same JS. It is what lets a team rename `.js` → `.ts` on day one and ship.

### 2.2 Type erasure as a core semantic property

Design goal G9 ("fully erasable") and non-goal N5 (no runtime type information / no type-directed emit) mean the meaning of a TS program is (ideally) the meaning of the JS obtained by deleting its type annotations. The playground/handbook frame TS as a compile-time-only tool.

**The historical exceptions** — TS constructs with runtime semantics:
- `enum` (emits an object, with reverse mappings for numeric enums); `const enum` (inlined — requires cross-file type information, hence banned under `isolatedModules`).
- `namespace`/`module` with values (emits IIFEs).
- Parameter properties (`constructor(public x: number)` emits `this.x = x`).
- `import x = require(...)`, `import A = N.B`, `export =`.
- Legacy `experimentalDecorators` plus `emitDecoratorMetadata` (emits `design:type` metadata derived *from types* — the one place where TS emit literally depended on type information).
- Import elision: historically TS dropped imports only used as types, which *is* type-directed emit (fixed by `verbatimModuleSyntax`).

### 2.3 The isolation flags: making "just strip types" a contract

As third-party transpilers (Babel's TS preset, esbuild, swc, Sucrase, oxc) became dominant for *emit* while `tsc` was kept for *checking*, TS added flags that guarantee each file can be transformed alone, without a type checker:

| Flag | Version | Guarantee |
|---|---|---|
| `--isolatedModules` | 1.5 | Each file can be transpiled independently (no `const enum` across files, re-exported types must be marked, etc.). |
| `--verbatimModuleSyntax` | 5.0 | Imports/exports are emitted exactly as written except those marked `type`; no type-directed import elision. Node's docs: "the `type` keyword is necessary to correctly strip type imports" (https://nodejs.org/api/typescript.md). |
| `--isolatedDeclarations` | 5.5 | Every exported symbol has enough explicit annotation that `.d.ts` can be produced by a single-file syntactic transform, "with no type checker required", enabling parallel declaration emit by tools like oxc (https://oxc.rs/docs/guide/usage/transformer/isolated-declarations). |
| `--erasableSyntaxOnly` | 5.8 | Errors on TS constructs with runtime semantics: enums, namespaces with runtime code, parameter properties, `import =`/`export =`. Motivation stated in the 5.8 release notes: "it must be possible to easily *erase* or 'strip out' any TypeScript-specific syntax from a file, leaving behind a valid JavaScript file" (https://www.typescriptlang.org/docs/handbook/release-notes/typescript-5-8.html). |

### 2.4 Native type stripping in runtimes

- **Node.js.** Type stripping was added in v22.6.0 (`--experimental-strip-types`), enabled by default from v23.6.0 / v22.18.0, warning-free from v24.3.0, and marked **Stability 2 – Stable in v25.2.0 / v24.12.0**. `--experimental-transform-types` (which handled enums etc.) was **removed in v26.0.0** (https://nodejs.org/api/typescript.md). Node "will replace TypeScript syntax with whitespace, and no type checking is performed", so no source maps are needed; it "ignores `tsconfig.json`"; unsupported syntax (enums, runtime namespaces, parameter properties, import aliases) throws `ERR_UNSUPPORTED_TYPESCRIPT_SYNTAX`; `.tsx` is unsupported; and Node "refuses to handle TypeScript files inside folders under a `node_modules` path" to discourage publishing raw TS. The parser is Amaro (swc compiled to WebAssembly) (https://github.com/nodejs/amaro). Node recommends TS ≥5.8 with `erasableSyntaxOnly`, `verbatimModuleSyntax`, `rewriteRelativeImportExtensions`.
- **Bloomberg `ts-blank-space`**: a pure-JS stripper that replaces annotations with whitespace, preserving positions (https://github.com/bloomberg/ts-blank-space).
- **Deno** and **Bun** have executed TS directly since their 1.0 releases by transpiling (not type-checking) on load; Deno uses swc, Bun its own transpiler. Type checking is a separate step (`deno check`, `tsc --noEmit`).

**Why "just strip types" became load-bearing.** Once runtimes, bundlers, test runners and linters all treat TS as "JS with erasable annotations," the following hold *across the whole ecosystem*: (a) per-file transforms are parallel and fast; (b) stack traces line up without source maps; (c) you can run code with type errors; (d) the type checker is replaceable (tsc, tsgo, or none). TS 7's Go port can therefore change the checker wholesale without anyone's runtime breaking. A ProofScript that requires its own non-trivial emit pass would be excluded from all of this.

---

## 3. Gradual adoption mechanisms

TS offers a *ladder* where every rung is independently useful:

| Mechanism | What it does | Since |
|---|---|---|
| Rename `.js`→`.ts` | Works immediately because errors don't block emit. | 0.8 |
| `allowJs` | Mix `.js` and `.ts` in one program; TS files import JS and vice versa. | 1.8 |
| `checkJs` / `// @ts-check` | Type-check plain `.js` files, with types from inference and **JSDoc** (`@type`, `@param`, `@typedef`, `@template`). Zero syntax change, file stays runnable JS. | 2.3 |
| `// @ts-nocheck` | Opt a file out. | 2.3 (JS), 3.7 (TS) |
| `// @ts-ignore` | Suppress the error on the next line. | 2.6 |
| `// @ts-expect-error` | Suppress, but *error if there's nothing to suppress* (prevents stale suppressions). | 3.9 |
| `any` | Escape hatch at any granularity; implicitly inferred unless `noImplicitAny`. | 0.8 |
| `unknown` | Safe top type: must narrow before use. | 3.0 |
| `.d.ts` declaration files | Describe untyped JS libraries without touching them; DefinitelyTyped (`@types/*`) crowdsourced types for the ecosystem. | 0.8 / ~2012– |
| `strict` family | `noImplicitAny`, `strictNullChecks` (2.0), `strictFunctionTypes` (2.6), `strictPropertyInitialization`, `useUnknownInCatchVariables`, etc., individually opt-in; `strict` umbrella 2.3. **Default became `true` only in TS 7.0** (https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/), 13+ years later. | 2.3 |
| Extra-strict opt-ins | `noUncheckedIndexedAccess` (4.1), `exactOptionalPropertyTypes` (4.4) — never part of `strict`. | |
| Project references / `composite` | Split monorepos into independently checked units with `.d.ts` boundaries. | 3.0 |

Note TS 7.0 *tightened* JS/JSDoc checking (e.g. `@enum`, `@constructor` no longer recognized; `Object`≠`any` in JS) (https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025) — showing that once a language dominates it can afford to remove looseness that bootstrapped adoption.

### Migration case studies

- **Airbnb `ts-migrate`** (2020): a codemod pipeline that turns a JS project into a *compiling* TS project by inserting `any` (aliased `$TSFixMe`) and `// @ts-expect-error` wherever needed — the "reignore" step. "Projects with more than 50,000 lines of code and 1,000+ files" were converted in one day; 86% of a 6M-line frontend had been converted (https://www.infoq.com/news/2020/08/airbnb-typescript-migration, https://github.com/airbnb/ts-migrate). **Lesson:** migration is "make it compile with explicit debt markers, then pay down debt"; *suppression comments are a migration tool, not a smell*.
- **Stripe** (2022): migrated the Dashboard (3.7M+ lines) from Flow to TS in **one pull request**; automated conversion initially produced 97,000+ suppressions, reduced to 37,000 (vs ~5,000 suppressions under Flow) (https://stripe.com/blog/migrating-to-typescript). **Lesson:** even the "big bang" approach depends on suppressions; and the destination was TS because of ecosystem gravity.
- **Slack**: an early large TS adopter of a mixed JS/TS codebase; in 2026 it reported TS 7 cutting CI type-checking from ~7.5 to ~1.25 minutes (https://infoq.com/news/2026/08/typescript-7-released/). **Lesson:** checker performance at scale is an adoption feature.
- **Dropbox / mypy (Python analogue)**: gradual migration to 4M lines of annotated Python; performance (incremental checking, daemon, compiled mypyc) was "the main obstacle" (https://dropbox.tech/application/our-journey-to-type-checking-4-million-lines-of-python).

**Implications for ProofScript:** proofs must be adoptable at the granularity of a single function or even a single assertion; there must be a ProofScript `@ts-expect-error` analogue (e.g. `assume`/`sorry`/`admit` with an *audit trail*); and a ProofScript-checked file must coexist with unchecked `.ts` files in the same program.

---

## 4. Deliberate unsoundness

TS's handbook: "TypeScript's type system allows certain operations that can't be known at compile-time to be safe… The places where TypeScript allows unsound behavior were carefully considered" (https://www.typescriptlang.org/docs/handbook/type-compatibility.html). The playground soundness page frames design as a trade-off between Simplicity, Usability and Soundness, leaning to the first two "because TypeScript aims to support all JavaScript" (https://www.typescriptlang.org/play/typescript/language/soundness.ts.html).

Catalogue of known unsound spots (handbook + Dan Vanderkam's "Seven Sources of Unsoundness", https://effectivetypescript.com/2021/05/06/unsoundness):

1. **`any`** — assignable to and from everything.
2. **Type assertions** (`as`, `<T>`, non-null `!`) — unchecked.
3. **Unchecked index access** — `arr[i]` is `T` not `T | undefined` unless `noUncheckedIndexedAccess`.
4. **Inaccurate declarations** — `.d.ts` files are trusted, not checked against the implementation.
5. **Array covariance / mutable property covariance** — `Dog[]` assignable to `Animal[]`, then push a `Cat`.
6. **Method parameter bivariance** — `strictFunctionTypes` fixes function-typed *properties* but intentionally leaves *methods* bivariant (to keep e.g. `Array<T>` covariant and DOM event handlers usable).
7. **Optional/rest parameter compatibility**, and **narrowings not invalidated by calls** (a callback may mutate a narrowed property).
8. Others: `void`-returning callback substitutability, enum↔number assignability, structural `{}`/`Object`, class `private` erased at runtime, etc.

**Why it mattered for adoption.** Each unsound rule exists to admit a pervasive JS idiom (event listeners, covariant arrays, optional callbacks). A sound checker would reject large swaths of working code, making "rename to .ts and go" impossible and making `.d.ts` authorship for dynamic libraries infeasible. Every competitor that pushed soundness harder (Dart 2's sound mode, Flow's later strictness, Elm, PureScript) had a smaller addressable audience.

**Implication.** ProofScript *cannot* rest proofs on TS types as such: a TS type `number[]` does not guarantee the value is an array of numbers. Proofs must either (a) be about a *sound sub-language* in which the TS escape hatches are rejected or tracked, or (b) treat every TS type crossing into proof land as an **assumption** (like a `.d.ts` is). See §10.

---

## 5. Tooling as product

### 5.1 Language service first
TS shipped from day one as a compiler *and* a language service (`tsserver`) powering completions, quick info, rename, go-to-definition and refactors — and Microsoft built VS Code (2015) in TS with TS tooling built in. Commentators on why Flow lost cite exactly this: "VSCode has become the standard text editor… and it ships with built-in support for TypeScript" (https://dev.to/wemake-services/from-flow-to-typescript-why-1k7m). The language service also powers *JavaScript* IntelliSense in VS Code — millions of JS developers use TS without knowing it, which is the ultimate on-ramp.

### 5.2 TypeScript 7 / typescript-go ("Project Corsa") — status as of Nov 2026
- Announced March 2025; preview as `@typescript/native-preview` (8.5M+ weekly downloads).
- **TypeScript 7.0 released as stable on July 8, 2026** (https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/; InfoQ coverage dated Aug 2026: https://infoq.com/news/2026/08/typescript-7-released/). Full builds 7.7–11.9× faster (VS Code: 125.7s → 10.6s).
- TS 6.0 was the last JS-based release and a bridge; 7.0 turns 6.0 deprecations into errors (`target: es5`, `moduleResolution: node10/classic`, `baseUrl`, AMD/UMD/System modules, `alwaysStrict: false`…), and changes defaults (`strict: true`, `module: esnext`, `types: []`, `rootDir: ./`).
- **Editor protocol is now LSP**, replacing the bespoke tsserver protocol (https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025).
- **API story:** 7.0 ships *without* a programmatic API; the old JS ("Strada") API is not supported; "We expect TypeScript 7.1 to ship with a new (and different) API." A compatibility package `@typescript/typescript6` (`tsc6`) lets old tooling run side-by-side. "Projects using Vue, MDX, Astro, Svelte, and others will need to continue using TypeScript 6.0 for now"; Angular template checking also not yet supported. Issue "Support embedded JavaScript/TypeScript" (microsoft/TypeScript#63772) was closed on 2026-08-20 as "Implemented in microsoft/typescript-go#4712", suggesting a first-party embedded-language mechanism is landing for 7.1 — **details unverified; must be re-checked** before ProofScript commits to an integration strategy.

### 5.3 Language service plugins and their limits
Per the TS wiki "Writing a Language Service Plugin" (https://github.com/microsoft/TypeScript/wiki/Writing-a-Language-Service-Plugin): plugins only augment the *editor* experience (completions, diagnostics, go-to-def); they **cannot add new syntax, cannot change emit, and cannot change what `tsc` reports**, because they are not loaded by command-line `tsc`. Compiler-level extension has never been offered (people resort to forks like `ts-patch`). **So ProofScript cannot be a TS plugin.** It needs its own parser/checker front end that *produces* TS (or TS ASTs) for the rest of the toolchain.

### 5.4 Volar.js: how Vue/Astro/MDX/Svelte add languages on top of TS
Volar (https://volarjs.dev/) maps a custom file (e.g. `.vue`) into one or more **virtual TypeScript files** with source mappings; it runs the real TS language service on the virtual code and maps diagnostics/completions/rename back to the original. It powers the Vue, Astro and MDX language servers (Svelte has a similar `svelte2tsx` approach). It achieves this by wrapping/monkey-patching the TS API — which is exactly why TS 7 temporarily broke these frameworks. **This is the most directly relevant precedent for ProofScript tooling**: ProofScript files can be virtualised into `.ts` (proof parts erased or encoded as types/comments) for the TS service, while a ProofScript-specific checker handles proof obligations and merges diagnostics. The risk is coupling to an API that TS has just replaced; the 7.1 API and the #4712 embedded-language work should be tracked closely.

---

## 6. TC39 "Type Annotations" (types-as-comments) proposal

Source: https://github.com/tc39/proposal-type-annotations (README; fetched 2026-11-02).

- **Status:** Stage 1 (since March 2022). Champions: Daniel Rosenwasser (Microsoft), Romulo Cintra (Igalia), Rob Palmer (Bloomberg). The README says it "has not been updated regularly" and points to 2022–2023 plenary notes; I found no 2025/2026 advancement. Treat as **stalled but alive**.
- **Idea:** JS engines would *parse and ignore* type syntax, like comments. Proposed erasable syntax: variable/parameter/return annotations; `interface` and `type` declarations; class field annotations; optional parameters `x?:`; `import type`/`export type`; `as` assertions; non-null `x!`; generic parameter declarations on functions/classes/types; `this` parameters.
- **Grammar approach ("token soup"):** the "easy first step" is that anything inside matched `()`, `[]`, `{}`, `<>` after a type-introducing token can be skipped without understanding it; determining where an unbracketed type *ends* "is where things get harder" and is unresolved (see `syntax/grammar-ideas.md`).
- **Excluded:** enums, namespaces, parameter properties (they generate code); JSX; runtime reflection. **Generic call arguments** `f<T>(x)` cannot be used as-is because it is already valid JS (comparisons) — a `::<T>` form was floated, nothing proposed. Overloads, `declare`, and class modifiers (`public`, `private`, `readonly`, `abstract`, `override`) are "under consideration".

**Relevance.** If ProofScript's added syntax fits within the *same* erasable regions — after `:` in annotation position, inside `type`/`interface` declarations, inside bracket-delimited regions after a reserved introducer — then (a) generic TS strippers could be taught to drop it with a tiny grammar extension, and (b) if the TC39 proposal ever lands with a sufficiently permissive "token soup", ProofScript files could *run unmodified in JS engines*. Conversely, any ProofScript syntax at **expression level** (new operators, proof terms inline in expressions without a bracketed introducer) would forever require a ProofScript-aware transform. Design rule: *every ProofScript-only construct must be introduced by a keyword or punctuation in a position where the remainder is a bracket-balanced, skippable region*, ideally a whole declaration (e.g. `theorem foo … { … }` stripped as a unit, the way `interface` is).

---

## 7. Competitors that failed or stalled

| Language | Strategy | What happened | Lesson for a superset |
|---|---|---|---|
| **CoffeeScript** (2009) | New surface syntax, "It's just JavaScript" semantics. | Huge 2010–2014; collapsed as ES2015 absorbed its features (classes, arrows, destructuring) and its syntax couldn't track new JS. No types; no gradual path *back*. | Diverging syntax from the host makes you a casualty of host evolution. Track the host's grammar exactly. |
| **Dart 1** (2011) | New language; native Dart VM in Chrome (Dartium) plus dart2js. | Google abandoned the in-Chrome VM in March 2015 to focus on compiling to JS (https://www.i-programmer.info/news/98-languages/8429-dart-changes-course-no-longer-to-be-native-in-chrome.html); Dart 2 (2018) moved to a *sound* type system; found a second life only via Flutter. | Replacing the host fails; *interop and incremental migration* matter more than a nicer language. Soundness was affordable for Dart only because it was not a superset. |
| **Closure Compiler** | Types in JSDoc comments, coupled to an optimizing compiler; Google-internal. | Powerful but verbose, slow, Google-centric; Google itself moved large parts of its frontend to TS. Its ideas survive in TS's `checkJs` JSDoc support. | Comment-embedded types work technically but are unergonomic; tie-in to a single build pipeline limits adoption (TS non-goal N4). |
| **AtScript** (2014) | Google's TS superset with annotations + runtime type info, for Angular 2. | Merged into TS in March 2015; TS 1.5 adopted decorators (https://sdtimes.com/angular/google-microsoft-combine-typescript-atscript-angular-2/). | A superset-of-a-superset survives best by **converging upstream**, not forking. Runtime type info (AtScript's distinguishing feature) is what TS later regretted (`emitDecoratorMetadata`). Strong precedent for ProofScript: aim to be mergeable into TS, or at least never contradict it. |
| **Flow** (2014) | Erasable annotations on JS ("simply remove the type hints"); sounder than TS, global inference. | Lost to TS around 2018–2021: weaker editor tooling, frequent breaking changes, poor library typings (flow-typed vs DefinitelyTyped), performance/memory issues. May 2021 "Clarity on Flow's Direction" announced Facebook-internal priority and new syntax "beyond JavaScript with types" (https://flow.org/blog/2021/05/25/Clarity-on-Flows-Direction-and-Open-Source-Engagement/); since then added non-erasable `component`/`hook` syntax and `match` expressions (https://flow.org/en/docs/match/). Stripe, Jest, Yarn and others migrated off. | Being *technically* better (more sound) loses to ecosystem + tooling + stability. Once a tool serves only its owner and starts adding non-erasable syntax, external users leave. |
| **ReasonML / ReScript** | OCaml semantics with JS-like syntax; sound types; compiles to readable JS. | Community split (2020 rebrand), syntax churn, small ecosystem; remains niche. | Sound + separate language = niche even with good JS output. |
| **Elm** | Pure FP language for web apps; JS interop only through ports. | Elm 0.19 (2018) removed "native modules" for non-core packages, cutting off JS interop escape hatches; adoption stalled. | Removing escape hatches to protect guarantees kills adoption in heterogeneous codebases. |
| **PureScript** | Haskell-like, compiles to JS. | Niche. | Same. |
| **Hack** (2014) | Gradually typed PHP superset on HHVM; "most PHP files are already valid Hack files"; type checking incremental "even within a single file" (https://engineering.fb.com/2014/03/20/developer-tools/hack-a-new-programming-language-for-hhvm/). | Facebook migrated nearly its whole codebase in a year — the superset strategy worked internally. Then HHVM 3.30 was the last PHP-compatible series; HHVM 4.0 (Feb 2019) "no longer aim[s] to be compatible with PHP" (https://hhvm.com/blog/2018/09/12/end-of-php-support-future-of-hack.html, https://hhvm.com/blog/2019/02/11/hhvm-4.0.0.html). External adoption evaporated; PHP itself absorbed gradual types (PHP 7/8). | Superset + gradual typing is the *right* migration strategy; abandoning the superset after the owner finishes migrating forfeits the wider community. The host language may then absorb the best ideas (as TC39 may with type annotations). |

---

## 8. Verification layers over mainstream languages — what adoption pattern worked

| Tool | Host | Embedding | Erasure | Adoption notes |
|---|---|---|---|---|
| **SPARK 2014** | Ada | Ada 2012 *aspects* (`Pre`, `Post`, `Contract_Cases`, `Loop_Invariant`), ghost code; a *subset* of Ada. | Ghost code "can be removed when the final executable is built, and GNATprove checks that ghost code has no effect on program behavior" (AdaCore). | Most successful industrial example (avionics, rail, NVIDIA firmware root of trust: https://www.adacore.com/uploads/case-studies/NVIDIA-Adoption-of-SPARK-Ushers-in-a-New-Era-in-Security-Critical-Software-Development.pdf). Graduated **assurance levels**: Stone (valid SPARK subset), Bronze (data/init flow), Silver (absence of runtime errors), Gold (key integrity properties), Platinum (full functional correctness, "seldom applicable due to the high cost"); recommendation: "use Bronze level for as large a part of the code as possible" (https://blog.adacore.com/new-guidance-for-adoption-of-spark). SPARK and non-SPARK Ada mix per-unit via `SPARK_Mode`. |
| **Liquid Haskell** | Haskell | Refinement types in `{-@ … @-}` special comments; a GHC plugin since 0.8.10 (https://well-typed.com/blog/2020/08/implementing-a-ghc-plugin-for-liquid-haskell). | Comments ⇒ trivially erased. | Academic + some industry; mirror packages (`liquid-base`) add specs to existing libraries (≈ `.d.ts`). Plugin fragility across GHC versions is a recurring cost (https://tweag.io/blog/2024-05-30-lh-upgrades/). |
| **Verus** | Rust | `verus!{}` macro or `#[verus_spec]` attribute; `spec`/`proof`/`exec` modes; `ghost`/`tracked` variables. | Spec and proof code erased before compilation; verified program "can be stripped to recover the original Rust program" (https://arxiv.org/pdf/2409.13082). | Rapid growth (systems code, LLM-assisted proof work). Mode system is a key design idea: *exec code cannot call spec/proof code except inside `proof { }` blocks* (https://verus-lang.github.io/verus/guide/exec_attr.html). |
| **Creusot / Prusti** | Rust | `#[requires]`, `#[ensures]`, `#[invariant]` attributes. | Attributes become no-ops in normal builds (dummy macro crate when not under the creusot cfg) (https://creusot-rs.github.io/creusot/guide/tutorial.html). | Research-to-industry; verify only safe Rust subset. |
| **Kani** | Rust | `#[kani::proof]` harnesses, `kani::any()`, function contracts. | Harnesses are `cfg(kani)`-gated. | Used in production at AWS: harnesses run on every change in Firecracker and s2n-quic (https://www.amazon.science/publications/kani-a-model-checker-for-rust). *Bounded model checking ⇒ low annotation burden ⇒ easy adoption.* |
| **JML / OpenJML** | Java | `//@` and `/*@ … @*/` comments. | Comments. | Long-lived, mostly academic/teaching (https://www.openjml.org/). |
| **Frama-C / ACSL** | C | `/*@ requires …; ensures …; */` comments. | Comments. | Industrial use in nuclear/avionics/security (https://frama-c.com/html/acsl.html). |
| **Python PEP 484** | Python | Annotations (syntax since 3.0) + `.pyi` stubs + `# type: ignore`. | Annotations have no runtime checking: "no type checking happens at runtime"; "Python will remain a dynamically typed language, and the authors have no desire to ever make type hints mandatory, even by convention" (https://peps.python.org/pep-0484/). | Massive adoption (mypy, Pyright). Direct copy of the TS playbook: optional, erasable, stubs, ignore comments, external checker. |
| **Dafny** | — (separate language) | Own syntax; compiles to C#, Java, JS, Go, Python. | Ghost code erased on compilation. | Used at AWS (e.g. authorization engines) for *new, isolated* components; Cedar was modelled in Dafny, then in Lean, with differential random testing against production Rust (https://amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing, https://aws.amazon.com/blogs/opensource/lean-into-verified-software-development/). |
| **F\*** / Low\* | — | Separate language extracting to OCaml/F#/C. | Erasure of proofs/ghost terms at extraction. | HACL\*/EverCrypt verified crypto shipped into Firefox, Linux kernel and others — but as *generated* C, not by retrofitting existing code. |
| **Refined TypeScript (RSC)** | TS | Refinement types in TS, Liquid-Types inference, SSA for mutation (https://arxiv.org/abs/1604.02480, PLDI 2016). | Research. | Most direct prior art for ProofScript; showed feasibility on D3 and parts of the TS compiler, but never productised. Worth a dedicated follow-up study. |

**Pattern that worked:** (1) contracts/specs embedded *in the host's own syntax extension points* (attributes, aspects, comments, annotations); (2) **erasure is guaranteed and checked** (SPARK checks ghost code has no effect; Verus mode system); (3) **per-unit opt-in** with mixed verified/unverified code (SPARK_Mode, Verus `#[verifier::external_body]`, Kani harness-per-function); (4) **graduated assurance levels** where the cheapest levels are nearly automatic; (5) **spec-only mirror packages** for libraries; (6) production use arises in teams that need *one* critical component verified inside a larger conventional codebase. Separate verification languages (Dafny, F*, Lean) succeed when they *generate* code into the mainstream language or serve as executable reference models, not when they ask a team to rewrite.

---

## 9. Candidate hard requirements for ProofScript vs TypeScript

Each requirement is phrased as an invariant and justified by the research above.

### A. Superset & erasure

**R1. TS ⊆ ProofScript, with identical emit.** Every program accepted by `tsc` (for a given tsconfig, `.ts`/`.tsx`/`.mts`/`.cts`/`.d.ts`) is a valid ProofScript program, type-checks the same way at the TS level, and emits byte-identical (or semantically identical) JS. *Justification:* TS goal G7/G11 analogues; Hack's and TS's migration success; Flow/Hack's loss after breaking the superset.

**R2. No new ProofScript keyword breaks existing identifiers.** All ProofScript keywords are contextual (as TS's `type`, `satisfies`, `infer` are); there is no re-interpretation of any valid TS text (avoid repeating the `f<a>(b)` ambiguity). *Justification:* §2.1.

**R3. Full erasability by a syntactic, single-file stripping pass.** There exists a trivial, type-checker-free transform `strip: ProofScript → TS` (ideally whitespace-replacing, à la `ts-blank-space`/Node) such that `strip(p)` is valid TS and `emit(p) = tscEmit(strip(p))`. Composed with TS's own stripping, ProofScript (when using `erasableSyntaxOnly`-compatible TS) strips straight to JS. *Justification:* G9, N5, `--isolatedModules`, `--erasableSyntaxOnly`, Node/Deno/Bun/esbuild/swc reliance on stripping (§2.3–2.4).

**R4. Proofs never affect runtime behaviour or emit.** No ProofScript construct (theorem, proof term, ghost variable, spec function, refinement, dependent index) has runtime semantics; no emit is directed by proof or type results (no "proof-directed optimisation", no runtime reflection of specs). Ghost code that could affect execution is a *compile error* (as in SPARK/Verus). *Justification:* N5; SPARK ghost-code checking; Verus modes.

**R5. Verification failures do not block emit by default.** Like TS type errors, proof failures are diagnostics; blocking (`noEmitOnProofError`) is opt-in for CI. *Justification:* §2.1 "errors don't block emit"; gradual adoption.

**R6. Syntactic footprint confined to erasable, bracket-delimited regions.** ProofScript syntax appears only in type positions, declaration positions (`theorem … { }`, `lemma`, spec blocks), or keyword-introduced bracket-balanced regions — never as new expression-level operators. *Justification:* TS goal G8; TC39 type-annotations "token soup" (§6) keeps open the possibility that ProofScript runs natively in JS engines one day.

### B. Interop & incremental adoption

**R7. Bidirectional module interop.** ProofScript files import, and are imported by, `.ts`/`.js`/`.d.ts` files in the same program and in npm packages, with no wrappers. TS consumers see ordinary TS types (dependent/refined types degrade to their TS "shadow" types). *Justification:* `allowJs` interop; SPARK_Mode mixing.

**R8. Per-file, per-declaration, per-obligation opt-in.** A codebase can adopt ProofScript one function at a time; there are directives analogous to `@ts-check`/`@ts-nocheck`; and an obligation-level escape hatch analogous to `@ts-expect-error` (`admit`/`assume`/`sorry`) that is *recorded* and *reportable*. *Justification:* §3 ladder; Airbnb/Stripe suppressions; SPARK levels.

**R9. A comment/JSDoc encoding exists.** Specs and simple theorems can be written in comments (e.g. `/** @requires … @ensures … */`) in plain `.ts` (and ideally `.js`) files, so teams can try ProofScript without changing file extensions or build tooling. *Justification:* `checkJs`+JSDoc; Liquid Haskell, JML, ACSL, Closure.

**R10. Spec-only declaration files for third-party code.** A `.d.ts`-like mechanism (and a DefinitelyTyped-like community repo) lets users state *assumed* specifications for untyped/unverified libraries, explicitly marked as trusted axioms. *Justification:* `.d.ts`/DefinitelyTyped; Liquid Haskell mirror packages; Python `.pyi`.

**R11. Graduated assurance levels, all opt-in, with the cheap ones automatic.** e.g. Level 0: TS types; 1: refinement/totality checks discharged automatically (SMT/decision procedures); 2: absence of runtime errors (no out-of-bounds, no `undefined` deref, no unhandled exceptions); 3: key properties; 4: full functional correctness with interactive proofs. Strictness flags are individually opt-in, mirroring the `strict` family. *Justification:* SPARK Stone→Platinum; TS's 13-year path to `strict: true` default.

### C. Tooling

**R12. Editor experience is a first-class deliverable.** ProofScript ships an LSP server providing full TS language-service features on ProofScript files plus proof-state display, goal inspection and incremental re-checking. *Justification:* §5.1; Flow's loss.

**R13. Compose with, don't replace, TS tooling.** ProofScript must work with the stock `tsc`/`tsgo` for TS-level checking (on the stripped or virtualised output), with existing bundlers/runtimes via stripping, and with existing linters/formatters (or provide drop-in parsers). Integration via a Volar-style virtual-file mapping or TS 7.1's new API/embedded-language support. ProofScript *cannot* be a TS language-service plugin (plugins cannot add syntax or affect `tsc`). *Justification:* TS non-goal N4; §5.3–5.4.

**R14. Declaration emit stays single-file.** ProofScript public APIs require enough annotation for `.d.ts` and spec-declaration emit without whole-program analysis (`isolatedDeclarations` analogue); proof checking may be whole-program but must be incremental and cacheable per module. *Justification:* `--isolatedDeclarations`; Dropbox/mypy and TS 7 performance lessons.

**R15. Proof checking performance budget.** Proof checking is incremental, parallel, cached, and its cost is paid only where proofs are written; unannotated TS code incurs ~zero extra cost. *Justification:* mypy daemon/mypyc; TS 7's raison d'être; Flow's memory problems.

### D. Evolution & governance

**R16. Track TypeScript and TC39 exactly.** Every TS release's syntax is supported within a bounded lag; ProofScript never adds syntax that conflicts with plausible TS/TC39 syntax and reserves its constructs in places TS is unlikely to use. Ideally parts of ProofScript are upstreamable. *Justification:* G6; AtScript merging into TS; CoffeeScript obsolescence.

**R17. Stability and openness.** No frequent breaking changes; development driven by external users, not one owner's codebase. *Justification:* Flow's 2021 pivot; HHVM 4.0.

**R18. Adding ProofScript never introduces a runtime dependency.** No runtime library is required for proofs (any proof-related standard library is type-/ghost-level only and erased). *Justification:* TS non-goal N6; G3.

### E. Soundness boundary

**R19. Sound core, explicit trust boundary.** Within verified regions, the logic is sound (consistent kernel, small TCB, ideally a Lean-like kernel with independent checkers). Every place where unverified TS (or `any`, `as`, `!`, `.d.ts`, unchecked indexing, mutable aliasing) flows into verified code is either rejected or becomes an explicit, enumerable assumption. A tool can print the full list of assumptions/axioms a theorem depends on (cf. Lean's `#print axioms`). *Justification:* §4 (TS's unsoundness) + §8 (SPARK subset, Verus/Creusot safe-Rust restriction, Kani's conditional guarantees).

**R20. Never weaken TS.** ProofScript may report *additional* errors in opted-in regions but must not make previously-erroring TS code acceptable in ways that change TS's own judgments for non-ProofScript consumers. *Justification:* R1; trust of TS-only collaborators in the same repo.

---

## 10. Tensions and open problems

1. **TS's unsoundness vs. proof soundness.** TS types are not facts about runtime values (any, as, covariance, bivariance, unchecked indexing, lying `.d.ts`). Options: (a) a *sound sublanguage* (SPARK-style subset) with a different, stricter typing judgement inside verified code; (b) *refinement over runtime JS semantics* (RSC-style), ignoring TS's static types as evidence; (c) treat boundaries as assumptions plus optional **runtime contract checks at the boundary** — but runtime checks conflict with R4/G3 (zero overhead, no runtime semantics). Likely answer: a sound core with boundary assumptions; optionally a *separate*, opt-in tool emits runtime validators (Zod-style) without changing ProofScript's own emit.

2. **Dependent types vs. "no runtime type information" and erasure.** Dependent types mention runtime *values* in types; proofs must be erased but computationally relevant values must not be. Requires a clear phase/mode distinction (Verus `spec/proof/exec`, Lean/Idris "erased" quantities, F*'s `Ghost` effect). Erasure must remain syntactic (R3) — so the erasable/relevant distinction must be visible in the *syntax*, not inferred, or single-file stripping breaks.

3. **Executable specs require pure, total functions — but TS functions are effectful, partial, and mutable.** Reasoning about JS semantics (getters, proxies, prototype mutation, `this`, coercions, exceptions, async, mutation through aliases) is hard. The verified fragment will need a restricted, Lean-like pure functional subset for spec/proof code and a separate (likely separation-logic or ownership-style) story for exec code.

4. **"Avoid expression-level syntax" vs. inline proofs.** Assertions, loop invariants, termination measures and proof-step hints naturally live *inside* function bodies. They must be expressible as statement-level, keyword-introduced bracketed blocks (`proof { … }`, `invariant(…)` in a ghost position) that strip cleanly — or as calls to ghost intrinsics whose whole statement is erased.

5. **Structural typing vs. nominal proof objects.** TS is structural; propositions-as-types and inductive families in Lean are nominal. Need a principled embedding (e.g., branded/opaque types at the TS shadow level).

6. **TS type checker as a moving target.** TS changes inference and type-checking behaviour every 3–4 months, and the API is being replaced (7.1). If ProofScript's soundness relies on TS's checker, it inherits that churn; better to have an independent core checker and treat TS as a *front-end/ergonomics* layer only.

7. **Performance and decidability.** TS is fast because it is unsound and heuristic; proof checking (especially SMT-backed) can be slow and nondeterministic. Must keep proof cost local (R15), cache aggressively, and prefer decidable automation for low assurance levels.

8. **Tooling dependency on TS internals.** Volar-style integration was broken by TS 7. ProofScript's integration should rest on the most stable surfaces: (a) TS *source text* produced by stripping, (b) LSP, (c) the forthcoming 7.1 API — not private internals.

9. **Comment encoding vs. first-class syntax.** Comments (R9) maximise compatibility but are unergonomic (Closure's lesson); first-class syntax is ergonomic but needs stripping. Supporting both, with one being a mechanical translation of the other, is the TS `checkJs`/JSDoc precedent.

10. **Escape hatches vs. trust.** Adoption needs `admit`/`assume` (R8); trust needs those to be visible (R19). Every escape hatch must be tracked and surfaced (like `@ts-expect-error` erroring when unneeded, plus an assumption report).

---

## Sources

- TypeScript Design Goals — https://github.com/microsoft/TypeScript/wiki/TypeScript-Design-Goals
- TS Handbook, Type Compatibility ("A Note on Soundness") — https://www.typescriptlang.org/docs/handbook/type-compatibility.html
- TS Playground, Soundness — https://www.typescriptlang.org/play/typescript/language/soundness.ts.html
- Effective TypeScript, "The Seven Sources of Unsoundness in TypeScript" — https://effectivetypescript.com/2021/05/06/unsoundness
- TS Handbook, JSX — https://www.typescriptlang.org/docs/handbook/jsx.html
- TS 5.8 release notes (`--erasableSyntaxOnly`) — https://www.typescriptlang.org/docs/handbook/release-notes/typescript-5-8.html
- oxc isolated declarations — https://oxc.rs/docs/guide/usage/transformer/isolated-declarations
- Node.js TypeScript docs — https://nodejs.org/api/typescript.md ; Amaro — https://github.com/nodejs/amaro ; Node issue — https://github.com/nodejs/typescript/issues/24
- Bloomberg ts-blank-space — https://github.com/bloomberg/ts-blank-space
- Announcing TypeScript 7.0 — https://devblogs.microsoft.com/typescript/announcing-typescript-7-0/
- Progress on TypeScript 7 (Dec 2025) — https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025
- InfoQ, TypeScript 7 released — https://infoq.com/news/2026/08/typescript-7-released/
- Visual Studio Magazine on TS 7 — https://visualstudiomagazine.com/articles/2025/12/02/microsoft-gets-real-on-native-typescript-remake.aspx
- Embedded languages issue — https://github.com/microsoft/typescript-go/issues/648 (redirect of microsoft/TypeScript#63772)
- Writing a Language Service Plugin — https://github.com/microsoft/TypeScript/wiki/Writing-a-Language-Service-Plugin
- Volar.js — https://volarjs.dev/ ; Vue Volar 1.0 — https://blog.vuejs.org/posts/volar-1.0.html
- TC39 Type Annotations proposal — https://github.com/tc39/proposal-type-annotations
- GitHub Octoverse 2025 (TS #1 by contributors) — https://github.blog/2025-10-28-octoverse-a-new-developer-joins-github-every-second-as-ai-leads-typescript-to-1/
- Airbnb ts-migrate — https://github.com/airbnb/ts-migrate ; InfoQ — https://www.infoq.com/news/2020/08/airbnb-typescript-migration
- Stripe migration — https://stripe.com/blog/migrating-to-typescript
- Dropbox mypy — https://dropbox.tech/application/our-journey-to-type-checking-4-million-lines-of-python
- Flow direction (2021) — https://flow.org/blog/2021/05/25/Clarity-on-Flows-Direction-and-Open-Source-Engagement/ ; Flow match — https://flow.org/en/docs/match/ ; Flow→TS commentary — https://dev.to/wemake-services/from-flow-to-typescript-why-1k7m , https://tkdodo.eu/blog/flow-to-type-script-migration-journey
- Dart course change — https://www.i-programmer.info/news/98-languages/8429-dart-changes-course-no-longer-to-be-native-in-chrome.html ; Dart 2 — https://www.androidpolice.com/2018/08/07/dart-googles-home-grown-programming-language-reaches-version-2-0/
- AtScript/TS merger — https://sdtimes.com/angular/google-microsoft-combine-typescript-atscript-angular-2/ ; https://devblogs.microsoft.com/somasegar/typescript-3-angular/
- Hack — https://engineering.fb.com/2014/03/20/developer-tools/hack-a-new-programming-language-for-hhvm/ ; HHVM ending PHP — https://hhvm.com/blog/2018/09/12/end-of-php-support-future-of-hack.html ; HHVM 4.0 — https://hhvm.com/blog/2019/02/11/hhvm-4.0.0.html
- PEP 484 — https://peps.python.org/pep-0484/
- Liquid Haskell plugin — https://well-typed.com/blog/2020/08/implementing-a-ghc-plugin-for-liquid-haskell ; Tweag LH upgrades — https://tweag.io/blog/2024-05-30-lh-upgrades/
- Verus — https://verus-lang.github.io/verus/guide/exec_attr.html ; AutoVerus — https://arxiv.org/pdf/2409.13082
- Creusot — https://creusot-rs.github.io/creusot/guide/tutorial.html ; https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md
- Kani — https://www.amazon.science/publications/kani-a-model-checker-for-rust
- SPARK adoption guidance — https://blog.adacore.com/new-guidance-for-adoption-of-spark ; NVIDIA case study — https://www.adacore.com/uploads/case-studies/NVIDIA-Adoption-of-SPARK-Ushers-in-a-New-Era-in-Security-Critical-Software-Development.pdf
- JML/OpenJML — https://www.openjml.org/ ; ACSL — https://frama-c.com/html/acsl.html
- Cedar (Dafny, Lean) — https://amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing ; https://aws.amazon.com/blogs/opensource/lean-into-verified-software-development/
- Refinement Types for TypeScript (PLDI 2016) — https://arxiv.org/abs/1604.02480

*Unverified/flagged items:* exact semantics of typescript-go#4712 embedded-language support; whether TS 7.x supports language-service plugins; current TC39 status beyond Stage 1 (no 2025–26 advancement found); Deno/Bun details stated from background knowledge; JML/ACSL/F\*/HACL\* details from background knowledge.
