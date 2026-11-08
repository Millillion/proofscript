# Proof certificates

A certificate lets anyone check a ProofScript project's proofs **without Lean**: in CI, on a machine without a Lean toolchain, or months later. It is not trusted. A forged or stale certificate cannot make a theorem verify.

```bash
proofscript check --write-certificate   # prove with Lean, save proofscript.cert
proofscript check --certificate         # check against proofscript.cert, Node only
```

Commit `proofscript.cert` next to `tsconfig.json`. When a statement changes, the certificate no longer covers it, and that theorem needs Lean again. Run `--write-certificate` to refresh it.

## What a certificate is

The gzipped [lean4export](https://github.com/leanprover/lean4export) output of every declaration the check produced, with a one-line JSON header: the format version, the Lean toolchain, and the lean4export commit. It includes your theorems and definitions, their proof terms, the Lean library declarations those proofs use, and one equation per definition (below). `examples/math`'s is 2.1 MB.

## How it is checked

1. **Kernel.** ProofScript's kernel re-checks every declaration in the certificate, exactly as after a check with Lean.
2. **Binding.** The project is translated again, from the current TypeScript. Each generated declaration is *elaborated by ProofScript itself*: a parser for the generated Lean (`lean-syntax.ts`) and a small elaborator (`elab.ts`, with unification and instance resolution). The kernel then checks that the certificate's declaration has exactly that type (definitional equality).
   - **Theorems:** the statement.
   - **Definitions:** the signature, and the equation `f params = body`, which Lean proves when the certificate is made. For a recursive function, also its uniqueness theorem: only one function satisfies the equation. So the certificate's function is the one written in TypeScript.
   - **Inductive types:** the type, and the constructors with their types, in order.
   - **Proofs are never elaborated.** Where the source has a proof (an index bound, a precondition at a call, a `have`), the elaborated term has a hole. Proof irrelevance makes the hole equal to any proof of the same proposition. The certificate must still contain such a proof, and the kernel checks it.
3. **Library.** Every Lean library constant a bound statement depends on, through types and definition bodies, must be the pinned toolchain's own. `packages/checker/src/library.json` holds content hashes (458 constants), generated from Lean by `packages/checker/scripts/library.ts`. A certificate that redefined `Nat.add` or `LT.lt` would be caught here. Library *theorems* need no such check: the kernel proves them, and which proof is used cannot change a statement's meaning.
4. **Axioms.** A result's axioms are listed as usual. A certificate whose `propext` (or other standard axiom) is not Lean's is rejected.

A theorem verifies only if it, and everything its statement depends on, is bound. Anything else needs Lean, and is reported as such:

```
nat.ts:4:1: error: theorem add_comm is not covered by the certificate (the certificate's PS.src.nat.add_comm has a different statement); check with Lean
```

## What it trusts

- ProofScript's kernel, as always.
- The TypeScript → Lean translation, as always ("trusts the translation of …" in each result).
- The elaborator, for the meaning of generated statements. It is small and deliberately incomplete: whatever it cannot elaborate is not bound.
- Nothing about termination. An equation like `length xs = match xs with … 1 + length tail` determines `length` only because the recursion terminates. So for every recursive function the certificate also carries a uniqueness theorem: any `g` satisfying the same equation equals `length`. Lean proves it by induction along the function's own recursion; ProofScript elaborates its statement and binds it like the others. If Lean could not prove one, the result lists `f terminates (proved by Lean when the certificate was made)` as an assumption instead.

## Known gaps

- An equation Lean cannot elaborate leaves its definition not covered: replay reports `definition f is not covered by the certificate; check with Lean`, and results that depend on `f` are checked only with Lean. In `examples/base64`, `encodeTail` and `decodeTail` (a chain of `Array.set` on a parameter) hit a Lean failure ("unknown free variable") when their equations are restated, which also leaves `encodeInto` and `decodeInto`, which call them, uncovered. The 32 theorems still replay. To be fixed in 0.0.12.

## Evidence

`packages/checker/test/certificate.test.ts`:

- `examples/math` verifies 28/28 from its committed certificate, without Lean.
- Every good fixture's certificate replays with the same results as the check with Lean.
- **Forged with Lean itself** (the generated Lean edited, then built and exported): a theorem proved with a weaker statement; a definition that means something else, with an equation consistent with it; an inductive type with an extra constructor; a proof replaced by `sorry` (admitted, not verified).
- A corrupted proof term (rejected by the kernel); a redefined `Nat.add` (caught by library authentication); a certificate from another toolchain (not used).
- Edited TypeScript: a changed statement, a changed definition (only the theorems depending on it lose coverage), a new theorem.
