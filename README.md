# ProofScript

ProofScript is a planned variant of TypeScript with dependent types and formal verification built in. The goal is to let TypeScript developers prove properties of their programs in the language they already use.

## Status

ProofScript is in the research and design stage. There is no code to try yet. Watch this repository to follow the work.

- [Hard requirements](docs/design/01-requirements.md): what being a superset of TypeScript means for ProofScript, and where it must be sound.
- [Language design](docs/design/02-language-design.md): modes, erasure, the kernel, types, syntax and tooling.
- [Roadmap](docs/design/03-roadmap.md)
- [Surface syntax: ProofScript is written in TypeScript](docs/design/04-surface-syntax.md), with [working examples](docs/design/typescript-only/)
- Research: [why TypeScript won](docs/research/01-typescript-success-principles.md), [verification prior art](docs/research/02-verification-prior-art.md), [foundations and soundness](docs/research/03-foundations-and-soundness.md), [syntax and tooling](docs/research/04-syntax-and-tooling.md)

In the meantime, [Lasm](https://github.com/Millillion/lasm) is the working project for formally verified code in the JavaScript world. It compiles Lean 4 to WebAssembly for servers, serverless and edge functions, and the browser.

## Support

If you want to see ProofScript built, I'd appreciate your sponsorship: [github.com/sponsors/lastmjs](https://github.com/sponsors/lastmjs). It supports me and the work on all of the [Millillion](https://millillion.org) projects. My first goal is $250 a month, enough for one dedicated Claude Code account for Lasm.

## License

MIT, copyright Jordan Last. See [LICENSE](LICENSE).
