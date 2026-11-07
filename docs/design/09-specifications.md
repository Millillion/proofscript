# Specification predicates (design for 0.0.10)

Status: proposal, implementation in progress. Decision D43, pending Jordan's review.

## Problem

Refinements name ordinary boolean functions (`Is<typeof sorted>`), which run in JavaScript and are translated to Lean `Bool` definitions. Quantified properties cannot be written that way. "Every unit before `j` is the encoding of its group" is `∀ p < j, out[p] = unitAt(bytes, p)`, and `forall` cannot run. So loop invariants and postconditions cannot describe whole arrays. That is what the whole-array base64 round trip needs, and what most real specifications need.

## Proposal

A **specification predicate** is a function returning `boolean` whose body is a single expression that uses `forall` or `exists`:

```ts
export function encodedUpTo(out: readonly nat[], bytes: readonly nat[], j: nat): boolean {
  return forall((p: nat) => implies(p < j && p < out.length, out[p] === unitAt(bytes, p)));
}
```

- **In the logic** it is a proposition (`def encodedUpTo … : Prop`), usable in `Is`/`Holds`, in `x satisfies …;` invariants, in theorems, and in other specification predicates.
- **In running code** it cannot be called. A call from code that runs is an error ("specification predicates cannot run"). To JavaScript it is still a function, and calling it returns `true` (as `forall` does), so ProofScript rejects such calls instead.
- **Proofs** about it use Lean's tactics as usual. For loop invariants, ProofScript's automatic tactic gets the facts it needs for array writes (`(a.set i v)[p] = if p = i then v else a[p]`) and splits on `p < j`. Invariants it cannot preserve automatically are proved with lemmas instantiated by `null satisfies Use<typeof lemma, […]>;` (D21).

## Alternatives

- **A `Spec` marker in the return type** (`boolean & Spec`): explicit, but more syntax for something the body already shows.
- **Executable bounded quantifiers only** (`xs.every((x, i) => …)` with an index): they run, but the specification is then about one array only, and `every` with an index needs callbacks in the logic (not yet supported).
- **Ghost code** (Dafny-style `ghost` functions): the general solution, and the eventual one; it needs a way to write it in TypeScript (ProofScript syntax is never comments, so likely a wrapper such as `ghost(() => …)`). Larger design, for after 0.1.0.

## Round trip plan

1. `encodeInto`: the invariant `encodedUpTo(out, bytes, j)` (each unit is `encodeUnit(sextet_r(group g))`), and then the postcondition for the tail.
2. `decodeInto`: `decodedUpTo(out, s, k)` (each byte is `byte_r(decodeUnit(…))` of its group's units).
3. A theorem composing them with `group_round_trip`, `decode_encode_unit` and `encode_unit_not_padding`. The statement is over `toBytes(fromBytes(x))`, a pure function in the logic that allocates the buffers and calls the two loops.
