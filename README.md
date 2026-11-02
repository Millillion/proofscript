# ProofScript

ProofScript is a TypeScript-based language prototype for writing code and machine-checked proofs in the same `.proof.ts` file.

The current surface language is pure TypeScript syntax. There are no custom keywords, no external proof language, and no JSDoc required in user code. You write:

- normal named TypeScript functions
- type-only markers that say which functions are specs and which implementations should match them
- proof helper calls inside loops

Then the ProofScript compiler:

1. lowers that source to plain TypeScript,
2. infers a proof strategy automatically,
3. emits runnable JavaScript, and
4. emits a proof artifact that records what was verified.

The end-to-end reference example is [examples/base64-js.proof.ts](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts), a ProofScript port of `beatgammit/base64-js`. Running `verify` on that file produces [proof-artifacts/base64-js.proof.json](/home/lastmjs/development/proofscript/proof-artifacts/base64-js.proof.json).

## Contents

- What ProofScript proves
- Quick start
- The core idea: spec function + implementation function
- Your first ProofScript file
- The surface language
- Finite domains and exhaustive proofs
- Loops
- Recursion
- Modeling invalid input and thrown errors
- What `verify` emits
- Current proof strategies
- Rules, limits, and sharp edges
- Reading the `base64-js` example
- FAQ

## What ProofScript Proves

If you are new to formal verification, the easiest way to think about ProofScript is:

- A test says: "I checked these examples."
- A ProofScript proof says: "I established that this implementation matches this specification for all cases covered by one of the verifier's proof rules."

Today, ProofScript is not a single all-powerful theorem prover. It is a growing proof engine with several automatic proof rules. When a function verifies, that proof is real, but it is real under a specific rule:

- exhaustive enumeration over a finite input domain
- structural equivalence between implementation and spec
- specific recursive cursor-scan patterns
- specific loop accumulator patterns

This means two things are true at once:

- verified functions really are checked, not just tested
- the language is still a prototype with a limited set of proof shapes

The proof artifact records exactly which rule was used for each theorem.

## Quick Start

Install dependencies, build the compiler, verify the example, and compile it to JavaScript:

```bash
npm install
npm run build
node dist/cli.js verify examples/base64-js.proof.ts
node dist/cli.js compile examples/base64-js.proof.ts
```

What these commands do:

- `verify` compiles the module, checks every generated theorem, and writes a `.proof.json` artifact
- `compile` only emits runnable JavaScript

Outputs:

- compiled JavaScript goes into `.proofscript-build/`
- proof artifacts go into `proof-artifacts/`

## The Core Idea: Spec Function + Implementation Function

In ProofScript, the main contract for a function is not written as a postcondition string. It is written as another function.

- The spec function says what the behavior should be.
- The implementation function is the code you want to ship.
- A type-only marker tells ProofScript that the implementation must match the spec.

That is the most important idea in the language.

### Why use a spec function?

Because executable specifications are easy to understand:

- they are plain TypeScript
- they can be slower and clearer than the optimized implementation
- they can be composed from smaller specs
- they can model valid and invalid behavior directly

For most developers, this is easier to learn than theorem syntax.

## Your First ProofScript File

Start with the smallest possible example:

```ts
export function chooseLeftSpec(x: number, y: number): number {
  return x;
}

export function chooseLeft(x: number, y: number): number {
  return x;
}

declare const chooseLeftSpecProof: ProofScriptSpec<typeof chooseLeftSpec>;
declare const chooseLeftProof: ProofScriptImpl<typeof chooseLeft, typeof chooseLeftSpec>;
```

What this means:

- `chooseLeftSpec` is the reference behavior
- `chooseLeft` is the real implementation
- `ProofScriptSpec<typeof chooseLeftSpec>` marks the spec as a spec
- `ProofScriptImpl<typeof chooseLeft, typeof chooseLeftSpec>` says the implementation must match that spec

The names of the marker declarations do not matter. Only their types matter.

This verifies today by an inferred `composition` proof, because the implementation body and spec body are structurally identical.

## The Surface Language

ProofScript currently relies on five user-facing surface constructs:

1. named function declarations
2. `ProofScriptSpec<typeof fn>` markers
3. `ProofScriptImpl<typeof impl, typeof spec>` markers
4. `proofscriptInvariant(...)` and `proofscriptDecreases(...)` at the top of loop bodies
5. `proofscriptAssert(...)` for inline assertions

### 1. Named function declarations

Use normal named TypeScript function declarations:

```ts
export function hexNibbleSpec(n: number): string {
  return "0123456789abcdef"[n] as string;
}

export function hexNibble(n: number): string {
  return "0123456789abcdef"[n] as string;
}
```

Important:

- named function declarations are currently the supported function form
- arrow functions and class methods are not recognized by the current verifier

### 2. Spec markers

Mark a function as a spec with a type-only declaration:

```ts
declare const hexNibbleSpecProof: ProofScriptSpec<typeof hexNibbleSpec>;
```

This declaration is for the ProofScript compiler. It is not runtime code.

### 3. Implementation markers

Link an implementation to a spec with:

```ts
declare const hexNibbleProof: ProofScriptImpl<typeof hexNibble, typeof hexNibbleSpec>;
```

This says:

"Prove that `hexNibble` behaves like `hexNibbleSpec`."

### 4. Loop helpers

ProofScript uses normal TypeScript call syntax for loop annotations:

```ts
for (let i = 0; i < xs.length; i += 1) {
  proofscriptInvariant(0 <= i && i <= xs.length);
  proofscriptDecreases(xs.length - i);
  out.push(renderSpec(xs[i]));
}
```

Current rules:

- these helper calls must be the first consecutive statements in the loop body
- if they are not first, the current frontend will not recognize them as loop annotations
- `proofscriptInvariant(...)` and `proofscriptDecreases(...)` are compile-time annotations and are erased from emitted JavaScript when used in the recognized position

### 5. Inline assertions

Use:

```ts
proofscriptAssert(total >= 0);
```

Unlike loop annotations, `proofscriptAssert(...)` is not erased. The compiler injects a runtime helper that throws if the condition is false.

Today this is useful for:

- documenting local facts
- catching bad assumptions in emitted JavaScript
- making proof intent clearer to human readers

The current verifier does not yet use assertions as a full logical assumption system.

## Finite Domains and Exhaustive Proofs

If every parameter of an implementation function has a recognized finite domain type, ProofScript can verify the function by exhaustive enumeration.

That means:

- it runs the implementation and the spec on every value in the domain
- it checks that the outputs are equal
- it records the number of checked cases in the proof artifact

### Built-in finite domains

The current compiler knows these domain types:

| Type | Meaning | Number of values |
| --- | --- | ---: |
| `Byte` | integers `0..255` | 256 |
| `Sextet` | integers `0..63` | 64 |
| `CodeUnit` | integers `0..65535` | 65,536 |
| `CodeUnitString` | `String.fromCharCode(0..65535)` | 65,536 |
| `Base64Char` | Base64 alphabet plus `-` and `_` | 66 |

These domains are currently built into the compiler. User-defined finite domains are not yet part of the surface language.

### Example: exhaustive proof over bytes

```ts
export type Byte = number;

export function invertByteSpec(b: Byte): number {
  return 0xff - b;
}

export function invertByte(b: Byte): number {
  return b ^ 0xff;
}

declare const invertByteSpecProof: ProofScriptSpec<typeof invertByteSpec>;
declare const invertByteProof: ProofScriptImpl<typeof invertByte, typeof invertByteSpec>;
```

Because `b` is a `Byte`, ProofScript can check all 256 possible inputs.

### Real example from `base64-js`

In [examples/base64-js.proof.ts](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts), this function verifies exhaustively over all 65,536 single UTF-16 code-unit strings:

```ts
export function charToSextetSpec(char: CodeUnitString): number {
  const directIndex = BASE64_ALPHABET.indexOf(char);
  if (directIndex >= 0) {
    return directIndex;
  }
  if (char === "-") {
    return 62;
  }
  if (char === "_") {
    return 63;
  }
  return 0;
}

export function charToSextet(char: CodeUnitString): number {
  return revLookup[char.charCodeAt(0)] ?? 0;
}

declare const charToSextetSpecProof: ProofScriptSpec<typeof charToSextetSpec>;
declare const charToSextetProof: ProofScriptImpl<typeof charToSextet, typeof charToSextetSpec>;
```

The proof artifact reports `checkedCases: 65536`.

## Composition Proofs

If a function is not finite-domain exhaustive, the verifier may still prove it by structural composition.

In plain terms, a `composition` proof means:

- the implementation and spec have the same shape
- variable names may differ
- already-proved helper functions may stand in for each other

This is especially useful for:

- wrappers
- arithmetic helpers
- functions that throw the same errors in the same branches

### Example

```ts
export function normalizeSpec(value: number): number {
  if (value < 0) {
    return 0;
  }
  return value;
}

export function normalize(value: number): number {
  if (value < 0) {
    return 0;
  }
  return value;
}

declare const normalizeSpecProof: ProofScriptSpec<typeof normalizeSpec>;
declare const normalizeProof: ProofScriptImpl<typeof normalize, typeof normalizeSpec>;
```

This is not exhaustive, because `number` is not a finite domain. But the bodies are structurally identical, so it can verify by composition.

### Composition with helper dependencies

The verifier can also prove a function compositionally when the implementation calls a proved helper and the spec calls the matching spec helper.

That is how many wrapper functions in the `base64-js` example verify.

## Loops

ProofScript can currently infer three loop-shaped proof rules:

- `loopJoin`
- `loopJoinTail`
- `loopWrite`

All of them rely on recognizable loop structure. The loop annotations (`proofscriptInvariant` and `proofscriptDecreases`) are useful documentation and future-facing proof hooks, but the current prototype still relies heavily on loop shape.

### `loopJoin`: push helper results, then join

This rule recognizes functions that:

- create an array accumulator like `const output: string[] = []`
- iterate with a `for` loop
- end each loop iteration with `output.push(helper(...))`
- return `output.join("...")`

Example:

```ts
export function encodeChunkSpec(uint8: ByteArray, start: number, end: number): string {
  const output: string[] = [];

  for (let i = start; i < end; i += 3) {
    proofscriptInvariant(start <= i && i <= end);
    proofscriptInvariant((i - start) % 3 === 0);
    proofscriptDecreases(end - i);
    output.push(tripletBytesToBase64Spec(uint8[i], uint8[i + 1], uint8[i + 2]));
  }

  return output.join("");
}

export function encodeChunk(uint8: ByteArray, start: number, end: number): string {
  const output: string[] = [];

  for (let i = start; i < end; i += 3) {
    proofscriptInvariant(start <= i && i <= end);
    proofscriptInvariant((i - start) % 3 === 0);
    proofscriptDecreases(end - i);
    output.push(tripletBytesToBase64(uint8[i], uint8[i + 1], uint8[i + 2]));
  }

  return output.join("");
}

declare const encodeChunkSpecProof: ProofScriptSpec<typeof encodeChunkSpec>;
declare const encodeChunkProof: ProofScriptImpl<typeof encodeChunk, typeof encodeChunkSpec>;
```

In the current `base64-js` proof artifact, `encodeChunk` verifies as `loopJoin`.

### `loopJoinTail`: loop join plus tail-case pushes

This rule is for functions that:

- build an array accumulator in a loop
- push chunk results during the loop
- then have one or more top-level `if` / `else if` tail cases that also push helper results
- finally return `accumulator.join(separator)`

That is how [fromByteArray](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts) verifies in the `base64-js` example.

### `loopWrite`: write into an output array or typed array with a cursor

This rule recognizes functions that:

- allocate an accumulator with `new ...`
- maintain a cursor such as `curByte`
- write with statements shaped like `arr[curByte++] = ...`
- return the accumulator at the end

Small example:

```ts
export function copyBytesSpec(xs: ByteArray): Uint8Array {
  const out = new Uint8Array(xs.length);
  let cursor = 0;

  for (let i = 0; i < xs.length; i += 1) {
    proofscriptInvariant(0 <= i && i <= xs.length);
    proofscriptInvariant(0 <= cursor && cursor <= out.length);
    proofscriptDecreases(xs.length - i);
    out[cursor++] = xs[i];
  }

  return out;
}

export function copyBytes(xs: ByteArray): Uint8Array {
  const out = new Uint8Array(xs.length);
  let cursor = 0;

  for (let i = 0; i < xs.length; i += 1) {
    proofscriptInvariant(0 <= i && i <= xs.length);
    proofscriptInvariant(0 <= cursor && cursor <= out.length);
    proofscriptDecreases(xs.length - i);
    out[cursor++] = xs[i];
  }

  return out;
}

declare const copyBytesSpecProof: ProofScriptSpec<typeof copyBytesSpec>;
declare const copyBytesProof: ProofScriptImpl<typeof copyBytes, typeof copyBytesSpec>;
```

In the `base64-js` example, [toByteArray](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts) verifies as `loopWrite`.

## Recursion

The current pure TypeScript surface automatically infers one recursive rule today: `recursiveAdvance`.

This rule is for recursive cursor scans with this shape:

1. an input parameter and an index parameter
2. a base case like `if (index === input.length) return ...`
3. a match case like `if (input[index] === "...") return ...`
4. a recursive return like `return helper(self(input, index + 1))`

### Example pattern

```ts
export function advanceMatchSpec(value: number): number {
  if (value === -1) {
    return -1;
  }
  return value + 1;
}

export function advanceMatch(value: number): number {
  if (value === -1) {
    return -1;
  }
  return value + 1;
}

export function firstBangFromSpec(text: string, index: number): number {
  if (index === text.length) {
    return -1;
  }
  if (text[index] === "!") {
    return 0;
  }
  return advanceMatchSpec(firstBangFromSpec(text, index + 1));
}

export function firstBangFrom(text: string, index: number): number {
  if (index === text.length) {
    return -1;
  }
  if (text[index] === "!") {
    return 0;
  }
  return advanceMatch(firstBangFrom(text, index + 1));
}

declare const advanceMatchSpecProof: ProofScriptSpec<typeof advanceMatchSpec>;
declare const advanceMatchProof: ProofScriptImpl<typeof advanceMatch, typeof advanceMatchSpec>;
declare const firstBangFromSpecProof: ProofScriptSpec<typeof firstBangFromSpec>;
declare const firstBangFromProof: ProofScriptImpl<typeof firstBangFrom, typeof firstBangFromSpec>;
```

This is the same pattern used by [firstPaddingIndexFrom](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts) in the `base64-js` example.

## Modeling Invalid Input and Thrown Errors

The current pure TypeScript surface does not have a general `requires` language.

Instead, you usually model invalid input behavior directly in the spec and implementation:

- return the same value for invalid input, or
- throw the same error in the same branch

Example:

```ts
export function validLengthSpec(text: string): number {
  if (text.length % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  return text.length;
}

export function validLength(text: string): number {
  if (text.length % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  return text.length;
}

declare const validLengthSpecProof: ProofScriptSpec<typeof validLengthSpec>;
declare const validLengthProof: ProofScriptImpl<typeof validLength, typeof validLengthSpec>;
```

This is exactly how `getLens` behaves in the `base64-js` example: the spec and implementation both throw on malformed Base64 length.

## What `verify` Emits

Running:

```bash
node dist/cli.js verify examples/base64-js.proof.ts
```

returns JSON like:

```json
{
  "emittedJavaScriptPath": "/.../.proofscript-build/base64-js.proof.js",
  "proofArtifactPath": "/.../proof-artifacts/base64-js.proof.json",
  "proofArtifact": {
    "modulePath": "/.../examples/base64-js.proof.ts",
    "verifiedAt": "2026-03-14T22:23:57.566Z",
    "theorems": [
      {
        "name": "charToSextetMatchesSpec",
        "kind": "exhaustive",
        "implementation": "charToSextet",
        "specification": "charToSextetSpec",
        "checkedCases": 65536,
        "bindings": [
          {
            "name": "char",
            "domain": "CodeUnitString"
          }
        ]
      }
    ]
  }
}
```

Why this matters:

- the artifact is the machine-readable proof record
- it tells you which proof rule verified each function
- it records checked case counts for exhaustive proofs
- it records helper dependencies for structural proofs

## Current Proof Strategies

You do not annotate proof kinds in user code. The compiler infers them.

Still, it is useful to understand what the verifier is trying to infer.

| Inferred kind | What it is for | How it is recognized today |
| --- | --- | --- |
| `exhaustive` | finite-domain equivalence | every parameter type is a built-in finite domain |
| `composition` | structural equivalence | implementation and spec have matching AST shape modulo proved helpers |
| `recursiveAdvance` | cursor-based recursive scans | `if` / `if` / `return helper(self(input, index + 1))` pattern |
| `loopJoin` | loop builds array, then joins | `push(helper(...))` in loop and final `join(...)` |
| `loopJoinTail` | loop join with tail-case pushes | same as `loopJoin`, plus top-level tail `if` branches |
| `loopWrite` | typed-array or array writes | accumulator allocated with `new`, writes via `acc[index++] = ...` |

### Internal note

The verifier backend also has a `recursiveChunk` theorem form, but the current pure TypeScript front end does not synthesize that proof kind automatically yet.

## Rules, Limits, and Sharp Edges

This section is intentionally blunt. It is here to help you succeed quickly.

### Use ProofScript's compiler entry points, not raw `tsc`

Run:

```bash
node dist/cli.js verify path/to/file.proof.ts
node dist/cli.js compile path/to/file.proof.ts
```

Do not expect plain `tsc path/to/file.proof.ts` to work as the ProofScript compiler. The ProofScript frontend injects compile-time support for `ProofScriptSpec` and `ProofScriptImpl` during lowering.

### Use named function declarations

Supported:

```ts
export function helper(x: number): number {
  return x;
}
```

Not currently supported as proof targets:

- arrow functions
- anonymous functions
- class methods

### Marker names do not matter

These are equivalent:

```ts
declare const a: ProofScriptSpec<typeof helperSpec>;
declare const b: ProofScriptImpl<typeof helper, typeof helperSpec>;
```

```ts
declare const helperSpecProof: ProofScriptSpec<typeof helperSpec>;
declare const helperProof: ProofScriptImpl<typeof helper, typeof helperSpec>;
```

Only the marker types matter.

### Loop helpers must be first

This works:

```ts
for (let i = 0; i < xs.length; i += 1) {
  proofscriptInvariant(0 <= i && i <= xs.length);
  proofscriptDecreases(xs.length - i);
  out.push(render(xs[i]));
}
```

This is not recognized correctly:

```ts
for (let i = 0; i < xs.length; i += 1) {
  out.push(render(xs[i]));
  proofscriptInvariant(0 <= i && i <= xs.length);
}
```

The loop helpers must be the first consecutive statements in the loop body.

### Finite domains are built in

At the moment, finite domains are defined in the compiler, not inside a `.proof.ts` file. If you want a new domain today, you have to add it in [src/domains.ts](/home/lastmjs/development/proofscript/src/domains.ts).

### Structure matters

ProofScript does not yet do arbitrary semantic reasoning over all JavaScript and TypeScript code.

If you hit an error like:

- `Unsupported node in ProofScript composition check`
- `ProofScript composition mismatch`
- `ProofScript loopWrite checker expected ...`

the usual fix is:

1. make the spec structurally closer to the implementation, or
2. break the code into smaller helpers and prove those helpers first

### Equality is implementation-aware

For exhaustive proofs, the generated theorem wrappers compare outputs using ProofScript's runtime equality helper:

- primitives by `===`
- arrays recursively
- typed arrays and other array-buffer views by byte contents
- other values by JSON fallback

That is good enough for the current prototype, but it is not a general semantic model of all JavaScript values.

## Reading the `base64-js` Example

The verified example in [examples/base64-js.proof.ts](/home/lastmjs/development/proofscript/examples/base64-js.proof.ts) is the best place to see the current language used seriously.

It demonstrates:

- `sextetAt` as an exhaustive proof over `Sextet`
- `tripletBytesToBase64` as an exhaustive proof over `Byte x Byte x Byte`
- `encodeChunk` as `loopJoin`
- `fromByteArray` as `loopJoinTail`
- `charToSextet` as an exhaustive proof over `CodeUnitString`
- `firstPaddingIndexFrom` as `recursiveAdvance`
- `getLens` as a composition proof that includes thrown-error behavior
- `toByteArray` as `loopWrite`

The proof artifact currently contains 18 generated theorems for this module.

The test suite in [test/base64.test.js](/home/lastmjs/development/proofscript/test/base64.test.js) checks both:

- that the proof artifact has the expected theorem inventory, and
- that the emitted module behavior matches the upstream `base64-js` implementation

## FAQ

### Do I have to write proof scripts separate from the code?

No. The spec, implementation, and proof markers all live in the same `.proof.ts` file.

### Do I need to understand theorem provers before using this?

No. The best way to learn it is:

1. write a simple spec function
2. write the implementation function
3. add the markers
4. verify
5. if it fails, simplify the spec or break helpers apart

You can get real value out of the system before learning formal methods terminology.

### Is the spec allowed to be slow?

Yes. That is often the point.

The implementation can be optimized and loop-heavy. The spec can be clearer and simpler.

### Is the spec allowed to call other spec helpers?

Yes. That is the normal style.

### Can one spec be used by multiple implementations?

Yes. The markers link implementations to specs by type reference.

### Do marker declarations emit JavaScript?

No. They are `declare const` declarations and exist only at compile time.

### Do loop annotations emit JavaScript?

`proofscriptInvariant(...)` and `proofscriptDecreases(...)` are erased when they appear in the recognized position at the top of a loop body.

`proofscriptAssert(...)` is different: it remains a runtime assertion.

### Can ProofScript prove every TypeScript program?

No. Not yet.

Today it can automatically verify several important patterns, and the `base64-js` example is proof that those patterns are already useful. But this is still a prototype, not a complete verifier for arbitrary TypeScript.

### What should I do when verification fails?

Usually one of these:

1. simplify the spec so it mirrors the implementation more clearly
2. extract a helper function and prove that helper first
3. switch finite-domain inputs to built-in domain types like `Byte` or `Sextet`
4. make loop structure match one of the current inferred loop forms
5. make recursive functions follow the cursor-scan shape used by `firstPaddingIndexFrom`

## Summary

If you remember only four things, remember these:

1. A ProofScript contract is usually a spec function, not a string annotation.
2. `declare const ...: ProofScriptSpec<typeof fn>` and `ProofScriptImpl<typeof impl, typeof spec>` are how you tell the compiler what to prove.
3. Loop annotations are ordinary helper calls written at the top of loop bodies.
4. The current verifier is real, but pattern-based. Write to the supported proof shapes and it can already verify nontrivial code like `base64-js`.
