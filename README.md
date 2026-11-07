# ProofScript

ProofScript is a planned variant of TypeScript with dependent types and formal verification built in. The goal is to let TypeScript developers prove properties of their programs in the language they already use.

## Status

ProofScript works end to end, in patch releases (0.0.x) on the way to the 0.1.0 MVP ([definition of done](docs/v0.1.md), [changelog](CHANGELOG.md)). It is not on npm yet.

```ts
import { omega, prove, type Ge, type Lt, type nat, type Proof } from "proofscript";

export function add_comm(a: nat, b: nat): Proof {
  return prove(a + b === b + a, omega);
}

export function pred(n: nat & Ge<1>): nat & Lt<typeof n> {
  return n - 1;
}
```

```
✓ add_comm — verified, axioms: Quot.sound, propext
✓ pred (postcondition Lt<typeof n>) — verified, …
```

- **Start here:** the [tutorial](docs/tutorial.md) and the [reference](docs/reference.md).
- **Examples:** [`examples/tutorial`](examples/tutorial), [`examples/math`](examples/math) (lists, insertion sort, inductive propositions, value-indexed vectors).
- **How it works:** TypeScript is translated to Lean, Lean proves (untrusted), and ProofScript's own kernel checks every proof. [Certificates](docs/certificates.md) let CI check proofs without Lean, and `proofscript audit` reports what each result rests on.
- **Evidence:** [status](docs/status.md). The kernel passes the Lean Kernel Arena (235 passed, 0 failed, 3 declined), and is differentially fuzzed against Lean's.

### Design

- [Hard requirements](docs/design/01-requirements.md): what being a superset of TypeScript means for ProofScript, and where it must be sound.
- [Language design](docs/design/02-language-design.md): modes, erasure, the kernel, types, syntax and tooling.
- [Roadmap](docs/design/03-roadmap.md)
- [Surface syntax: ProofScript is written in TypeScript](docs/design/04-surface-syntax.md), with [working examples](docs/design/typescript-only/)
- [Lean correspondence](docs/design/05-lean-correspondence.md): how each Lean 4 feature is written in ProofScript
- [Decision log](docs/design/06-decision-log.md): every decision so far, with the alternatives considered
- [Implementation plan and evidence strategy](docs/design/07-implementation-plan.md)
- [Lean's elaborator in WebAssembly](docs/design/08-lean-in-wasm.md): the planned replacement for the Lean dependency
- Research: [why TypeScript won](docs/research/01-typescript-success-principles.md), [verification prior art](docs/research/02-verification-prior-art.md), [foundations and soundness](docs/research/03-foundations-and-soundness.md), [syntax and tooling](docs/research/04-syntax-and-tooling.md)

Also see [Lasm](https://github.com/Millillion/lasm), the companion project for formally verified code in the JavaScript world. It compiles Lean 4 to WebAssembly for servers, serverless and edge functions, and the browser.

## Support

If you want to see ProofScript built, I'd appreciate your sponsorship: [github.com/sponsors/lastmjs](https://github.com/sponsors/lastmjs). It supports me and the work on all of the [Millillion](https://millillion.org) projects. My first goal is $250 a month, enough for one dedicated Claude Code account for Lasm.

## License

MIT, copyright Jordan Last. See [LICENSE](LICENSE).
