# Decisions for Jordan's review

Decisions with major trade-offs, large dependencies, architecture, developer-facing APIs, or the language syntax. Implementation continues on each; each is recorded in the [decision log](design/06-decision-log.md) with its alternatives. Review before 0.1.0.

## Language syntax and semantics

- **D6–D16, D29: the whole surface syntax** (`nat`, refinements `Lt<…>`, `Is<typeof p, […]>`, `satisfies` invariants, `prove`/`by`, tactic names). The syntax review against `examples/math`, `examples/tutorial` and `examples/base64`.
- **D35: bit operations.** Which operators, and with which obligations.
- **D36: predicates are stated by their bodies.** Affects what error messages show.
- **D37: modular automation.** Contracts become API: a proof can't see past a callee's postconditions.
- **D34: callers of functions with preconditions are verified code.** Changes which functions ProofScript checks.

## Developer-facing tools

- **CLI:** `proofscript check`, `proofscript audit`, `--write-certificate`, `--certificate`, `--json`; the certificate file name `proofscript.cert`; exit codes.
- **D33: certificates.** Format, what they trust, and termination taken from Lean.
- **Audit output** format, and the JSON schema.

## Dependencies and architecture

- **D39: one npm package**, with the TypeScript 6 compiler as a dependency.
- **D30/D31: Lean** as the proving engine, and its future replacement by WebAssembly.
- **D27: license** (MIT kept for now; Apache-2.0 or dual is the alternative).
- **CI** installs Lean (elan) from the internet, and the repository vendors 179 Lean Kernel Arena tests (Apache-2.0).
