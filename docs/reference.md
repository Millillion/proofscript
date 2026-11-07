# ProofScript reference

Version 0.0.8. The syntax is provisional until the syntax review (D29) before 0.1.0.

Everything ProofScript adds is exported by the `proofscript` package: types (which mean little or nothing to `tsc`) and a few runtime functions for theorems. The checker recognizes them by symbol, so they must be imported from `proofscript`; a local type named `Lt` is not ProofScript's `Lt`.

## Numbers

| Type | To `tsc` | To ProofScript |
|---|---|---|
| `nat` | `number` | A safe integer `>= 0`. Runtime arithmetic must stay within 2⁵³ − 1 (proved). |
| `int` | `number` | A safe integer. Runtime arithmetic must stay within ±(2⁵³ − 1) (proved). |
| `Nat` | `bigint` | A natural number, unbounded and exact. |
| `Int` | `bigint` | An integer, unbounded and exact. |
| `number` | `number` | Not in the logic: IEEE-754 floating point is not integer arithmetic. |

- **Subtraction on `nat` and `Nat`** must be proved not to go below zero. The proof comes from the context: a branch condition, a precondition, an invariant.
- **`Math.floor(a / b)`** on `nat` is floor division (`b > 0` proved). **`a % b`** on `nat` is the remainder (`b > 0` proved).
- **Bit operations** keep JavaScript's meaning:
  - `x & (2^k − 1)`, such as `x & 0xFF`, is `x mod 2^k` for any safe integer (JavaScript wraps to 32 bits first).
  - `x >> k` and `x >>> k` on `nat` are division by 2^k (with `x` below 2³¹ or 2³² proved).
  - `x << k` on `nat` is multiplication by 2^k (with the result below 2³¹ proved).
  - Other masks, and `|` and `^`, are not in the logic yet.
- **Arithmetic in theorems and specifications is exact.** The 2⁵³ limit applies to code that runs (D32).
- **Counting** (`1 + length(tail)`, and sums of up to 64 counts) is exempt from the overflow check, under the assumption `recursion depth below 2^30`, which results report.

## Refinements

A refinement is an intersection `T & R`. To `tsc`, every `R` below is `unknown`, so `T & R` is just `T`.

| Refinement | Meaning for a value `x` |
|---|---|
| `Lt<N>`, `Le<N>`, `Gt<N>`, `Ge<N>` | `x < N`, `x <= N`, `x > N`, `x >= N` |
| `Length<N>` | `x.length === N` (arrays and strings) |
| `Is<typeof p, [a, b]>` | `p(x, a, b)` holds, for an ordinary boolean function `p` |
| `Holds<typeof p, [a, b]>` | `p(a, b)` holds (no subject; for `void` functions and relations) |

`N` can be a literal (`Lt<10>`) or `typeof y`, the value of another parameter (`Lt<typeof n>`, `Lt<typeof a.length>`).

A predicate in `Is` or `Holds` whose body is a single expression (and that has no preconditions) is used by its body: `Is<typeof multipleOf3>` states `i % 3 === 0` itself. Arithmetic proofs then see the facts directly.

Where a refinement appears decides what it means:

| Where | Meaning |
|---|---|
| A parameter's type | **Precondition:** assumed in the body, and proved at every call in verified code |
| The return type | **Postcondition:** proved automatically, reported as a theorem `f (postcondition …)` |
| `x satisfies R;` at the top of a loop body | **Loop invariant:** proved on entry and after every iteration |
| A theorem's parameter | **Hypothesis** of the theorem |

### Frames and termination

| Type | Use |
|---|---|
| `Modifies<typeof a>` | In a return type: the function may change argument `a` (an array, or an object with mutable fields), and nothing else. |
| `Old<typeof a>` | In a postcondition's arguments: `a`'s value on entry (`typeof a` alone means its value on return). |
| `Decreases` | `e satisfies Decreases;` at the top of a loop body: a termination measure that decreases each iteration. |
| `Use<typeof lemma, [a, b]>` | `null satisfies Use<typeof lemma, [typeof a, typeof b]>;`: make an instance of a lemma available at this point. |

### Value-indexed types

A type parameter `n extends nat` ranges over values. Combined with refinement aliases, this gives dependent types:

```ts
type Vec<T, n extends nat> = readonly T[] & Length<n>;
type Fin<n extends nat> = nat & Lt<n>;

export function get<T, n extends nat>(xs: Vec<T, n>, i: Fin<n>): T {
  return xs[i]; // in bounds by the types
}
```

- **A value parameter determined by `Length<n>`** on a parameter is that parameter's length, and callers never supply it.
- **`Plus<A, B>` and `Times<A, B>`** are exact sums and products of indices, e.g. `Even<Plus<k, 2>>`.

## Data types

| TypeScript | Logic |
|---|---|
| A discriminated union (`{ tag: "nil" } \| { tag: "cons"; head: T; tail: List<T> }`) | An inductive type; each member is a constructor named by its `tag` |
| A plain object type or interface (`{ readonly x: nat; readonly y: nat }`) | A structure |
| `readonly T[]`, `T[]` | An array (`Array T`); indexing must be proved in bounds |
| `[A, B]` | A pair |
| `string` | A list of UTF-16 code units, as in JavaScript |
| `boolean` | `Bool`; in statements, a proposition |

`===` on numbers, booleans and strings is equality. On objects and arrays, JavaScript's `===` compares identity, not contents, so ProofScript rejects it; use `eq(a, b)` in statements for structural equality.

### Inductive propositions

An interface extending `Prop`, with its constructors in a `declare namespace`:

```ts
export interface Even<n extends nat> extends Prop { readonly __index: n }
export declare namespace Even {
  function zero(): Even<0>;
  function step<k extends nat>(h: Even<k>): Even<Plus<k, 2>>;
}
```

## Theorems

A theorem is a function that returns `Proof`, with a body of the form `return prove(statement, proof)`. Alternatively, a function whose return type is an inductive proposition (`Even<…>`) returns a proof of it.

| Function | Meaning |
|---|---|
| `prove(statement, proof)` | The theorem: `statement` is a boolean expression over the parameters (universally quantified) |
| `implies(p, q)` | p → q |
| `iff(p, q)` | p ↔ q |
| `eq(a, b)` | Structural equality |
| `forall((x: T) => p)`, `exists((x: T) => p)` | Quantifiers |
| `xs.every((x) => p)`, `xs.some((x) => p)`, `xs.includes(v)` | Bounded quantifiers over arrays |

Called at runtime, `prove` checks its statement on the given inputs and throws if it is false, so theorems are also property tests. `forall` and `exists` cannot be executed and return `true`.

`Proof & Simp` as the return type makes the theorem a simp lemma (Lean's `@[simp]`).

## Tactics

Proofs are Lean tactics, with Lean's names and behaviour (D13):

| ProofScript | Lean |
|---|---|
| `omega`, `decide`, `rfl`, `trivial`, `constructor`, `split`, `grind`, `sorry` | the same |
| `grind(l₁, …)`, `simp(l₁, …)`, `simp_all(l₁, …)`, `simp_only(l₁, …)` | `grind [l₁, …]`, `simp [l₁, …]`, `simp_all [l₁, …]`, `simp only [l₁, …]` |
| `rw(l₁, …)`, `unfold(f, …)` | `rw [l₁, …]`, `unfold f …` |
| `exact(e)`, `apply(e)`, `intro("h", …)` | `exact e`, `apply e`, `intro h …` |
| `induction(x, { ctor: (fields…, ihs…) => t })` | `induction x with \| ctor fields… ihs… => t` |
| `cases(x, { ctor: (fields…) => t })` | `cases x with \| ctor fields… => t` |
| `by(t₁, t₂, …)` | `t₁; t₂; …` (a tactic block) |
| `andThen(t₁, t₂, …)` | `t₁ <;> t₂ <;> …` |
| `attempt(t)` | `try t` (`try` is reserved in JavaScript) |
| `first(t₁, t₂, …)` | `first \| t₁ \| t₂ \| …` |
| `allGoals(t)` | `all_goals t` |
| `congrArg(f, h)` | `congrArg f h` |

Lemma arguments are TypeScript references: other theorems, functions to unfold, and induction hypotheses from the callbacks. A `sorry` makes a result *admitted*, never *verified*.

## Code in the logic

These functions are verified code:

- theorems;
- functions with a postcondition;
- functions with preconditions;
- functions that call a function with preconditions;
- every function they use.

A function used in the logic is translated to a definition that has JavaScript's meaning. Its translation is trusted, and named in each result ("trusts the translation of …").

**Supported:**

- **Statements:** `const` and `let`, assignment, `if`, `switch` on a tag, `return`, `while` and `for` (with invariants and a measure), `break` and `continue`.
- **Expressions:** arithmetic (`+ - *` on integers, `Math.floor(a / b)`), comparisons, `&& || !`, `?:`, calls, recursion, object and array literals.
- **Data:** field access, `a[i]`, `a.length`, `a.push(v)`, `a[i] = v`, `o.f = v`.
- **Array and string methods:** `includes`, `every`, `some`; `s.length`, `s.charCodeAt(i)`, `String.fromCharCode(c)` (with `c` below 2¹⁶ proved), `startsWith`, `endsWith`, and `+` on strings.

**Facts every proof may use:** an array has fewer than 2³² elements, and a string has at most 2⁵³ − 1 code units (ECMAScript guarantees both). After `const x = f(…)`, `f`'s proved postconditions hold of `x`.

**Not yet:**

- `number` (floating point), classes, `async`, generators;
- callbacks other than the array methods above, closures over mutable state;
- shared (aliased) mutable data;
- `throw` and `try`;
- most of the standard library.

Unsupported code in a verified function is an error. Unsupported code elsewhere stays ordinary TypeScript. A call from it to a function with preconditions is reported as unverified.

## Command line

```
proofscript check [options] [tsconfig.json | files…]
proofscript audit [options] [tsconfig.json | files…]

  --write-certificate [file]  prove with Lean and save a certificate (default: proofscript.cert)
  --certificate [file]        check against a certificate, without Lean
  --json                      (audit) print the audit as JSON
```

- **Exit status:** 0 when every theorem verified and there are no errors, 1 otherwise, 2 for usage errors.
- **Results:** each theorem is *verified*, *admitted* (depends on `sorry`) or *failed*. Its trust footprint lists the axioms it depends on, the reflected functions it trusts, and the assumptions it relies on.
- **Audit:** collects the footprints over the project, plus the boundary: exported functions with preconditions, and calls from unverified code. See [the tutorial](tutorial.md#7-what-do-my-results-rest-on-proofscript-audit).
- **Certificates:** see [certificates](certificates.md).

## Lean

Proving uses Lean as an untrusted engine (D30), pinned to `leanprover/lean4:v4.34.1`. The proofs it produces are exported and checked by ProofScript's own kernel, the only trusted checker. Lean's tools are found on `PATH` or in `~/.elan/bin`. lean4export is built at a pinned commit into `~/.cache/proofscript` (override with `PROOFSCRIPT_LEAN4EXPORT`). The generated Lean of a project is in `.proofscript/lean/PSGen.lean`.
