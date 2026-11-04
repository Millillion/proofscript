# examples/math

A small mathematics library written in TypeScript and proved with ProofScript. Every theorem is checked by ProofScript's kernel.

| Module | Contents |
|---|---|
| `src/nat.ts` | Arithmetic: commutativity, associativity, distributivity, transitivity, the square of a sum |
| `src/even.ts` | An inductive family of propositions (`Even<n>`), proofs by induction over it and over `nat` |
| `src/list.ts` | Immutable lists: `length`, `append`, `reverse`; `append` is associative, `reverse` is an involution and distributes over `append`, lengths add up |
| `src/sort.ts` | Insertion sort, proved to return a sorted list with the same elements (with multiplicities) and the same length |
| `src/vec.ts` | Value-indexed vectors: `Vec<T, n>`, `Fin<n>`, `replicate`, `zip`, `get` |

Check it (Lean must be installed; see the repository README):

```bash
node --stack-size=65500 ../../packages/checker/src/cli.ts check tsconfig.json
```
