# Lean's Elaborator in WebAssembly (Lasm Scope Note)

Status: **scope note v0.1** (2026-11-03). Context: [D30, D31](06-decision-log.md#d31-replacing-the-lean-dependency-webassembly-via-lasm--decided-2026-11-03).

## Goal

Run Lean's elaborator and tactic framework (`Lean.Elab`, `Lean.Meta`, `simp`, `omega`, `grind`, …) in-process in Node, compiled to WebAssembly, so that ProofScript (and any other tool) can turn Lean source into checked declarations without a native Lean installation.

ProofScript's interface to it is deliberately small:

```
elaborate(source: string, imports: Environment) -> { declarations (lean4export NDJSON), messages }
```

## What Lasm does today

Lasm compiles ordinary Lean programs ahead of time to WebAssembly for Node, including programs that `import Lean` (for example to use `Lean.Data.Json`). By design it excludes:

- runtime elaboration and evaluation;
- the C++ kernel and environment.

## What this capability needs

1. **Compile the elaborator as a library.** `Lean.Elab`/`Lean.Meta` are Lean code that Lasm can in principle already compile; the work is making the frontend entry points (`Lean.Elab.Frontend`, message collection) callable from JavaScript.
2. **The C++ pieces.** Lean's runtime parts that the elaborator calls (and `addDecl`'s kernel). Options: compile Lean's C++ kernel to WebAssembly with Lasm's C toolchain, or route `addDecl` to ProofScript's TypeScript kernel through a host import. ProofScript re-checks everything regardless.
3. **Environments.** Loading `.olean` data for `Init`, `Std` and `Lean` (and later Mathlib) into WebAssembly memory. Lean memory-maps `.olean` files natively; here they must be read into linear memory. Size (hundreds of MB), memory ceilings, and startup time are the main risks; a pre-built, compacted environment snapshot may be needed.
4. **The IR interpreter.** User-defined tactics, macros, `#eval` and environment extensions call compiled-or-interpreted code at elaboration time.
5. **Concurrency.** The elaborator uses `Task`s; WebAssembly threads in Node, or a single-threaded scheduler.
6. **GMP.** Big-number arithmetic in WebAssembly (Lasm already has a no-GMP configuration).

## Prior art to check

- Lean 4 has had an Emscripten build target in the past; its current state and limits should be checked before starting.
- The lean4web editor runs Lean on a server; that is the baseline this replaces.

## Milestones

1. Spike: elaborate a file that imports only `Init` and uses `simp`/`omega`; measure size, memory and time.
2. ProofScript drop-in: `lean.ts` gains an in-process engine behind the same interface; the test fixtures pass with no native Lean installed.
3. Std, then Mathlib-scale environments.

## Who else benefits

Lean in the browser without a server; AI agents running Lean in-process; editor tooling anywhere Node runs; teaching.
