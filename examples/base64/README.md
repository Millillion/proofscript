# examples/base64

A verified drop-in replacement for [base64-js](https://github.com/beatgammit/base64-js) 1.5.1: the same API (`byteLength`, `toByteArray`, `fromByteArray`), the same results, the same errors.

| File | Contents |
|---|---|
| `src/alphabet.ts` | The alphabet as arithmetic on code units (`encodeUnit`, `decodeUnit`, URL-safe `-` and `_`) |
| `src/group.ts` | The bit arithmetic of one group: three bytes are four sextets |
| `src/base64.ts` | Encoding and decoding loops, into preallocated buffers |
| `src/index.ts` | base64-js's API over them (allocation and type conversion; not verified) |

## What is proved

`proofscript check` verifies 32 theorems and every function in `alphabet.ts`, `group.ts`, `base64.ts` and `roundtrip.ts`:

- **Safety.** Every array and string access is in bounds, and every write lands inside the output buffer. No arithmetic overflows. Shifts and masks keep JavaScript's meaning: `x & 0xFF` is `x mod 256` for any safe integer.
- **Ranges.** Every encoded unit is an ASCII code of the alphabet (below 128), every decoded value a byte (below 256), every sextet below 64.
- **Buffers.** An output buffer of the base64 length (`⌈n/3⌉ · 4` characters) holds everything the encoder writes. One of `written(s)` bytes holds everything the decoder writes. Every write is proved inside the buffer.
- **Correctness, piece by piece:**
  - `decode_encode_unit`: every sextet survives the alphabet.
  - `group_round_trip`, `pair_round_trip`, `single_round_trip`: the sextets of any three bytes (or the padded one or two) decode back to those bytes.
  - `encode_unit_not_padding`: the alphabet never produces `=`, so the decoder finds the padding where the encoder put it.
  - `group_decodes`: decoding the units the encoder writes for any three bytes gives back those bytes (the composition, per group).
- **Whole-array specifications.** The encoder's loop proves `encodedWholeGroups`: every unit of every whole group is the right sextet's character. The decoder's loop proves `decodedGroups`: every byte of every complete group is decoded from its group's four characters. Both are quantified postconditions (specification predicates), maintained by loop invariants.

  The whole-array statement `toByteArray(fromByteArray(x)) = x` instantiates these two postconditions at each group and applies `group_decodes`. It is tested (below) but **not yet one theorem**: ProofScript has no tactic yet to instantiate a quantified hypothesis (decision D44, open).

## What is tested

- base64-js's own test suite, unmodified (`test/*.cjs`, MIT, see `test/LICENSE-base64-js`), including its 64 MB round trip: 57/57.
- A differential test against base64-js 1.5.1 (`test/differential.mjs`): 27,000 random inputs. These include URL-safe and invalid characters, unusual padding (`"AAAA===="`, `"=AAA"`) and integers outside 0–255. Every result, and every error, is identical.

## Differences from base64-js

- In the last, incomplete group, base64-js does not mask values outside 0–255. It looks them up anyway and emits the text `undefined`. This implementation masks them, as base64-js does for every whole group. For `Uint8Array` input, the documented API, the two are identical.

## Run it

```bash
../../packages/checker/bin/proofscript.mjs check
```

```bash
npm test
```

```bash
node --test test/differential.mjs
```
