// Base64 encoding and decoding with base64-js's behaviour, verified: every array access is
// in bounds, no arithmetic overflows, every output byte is a byte, and the output lengths
// are exact.
import { forall, implies, type Decreases, type Holds, type Is, type Le, type Modifies, type Old, type int, type nat } from "proofscript";
import { decodeUnit, encodeUnit } from "./alphabet.ts";
import { byte0, byte1, byte2, sextet0, sextet1, sextet2, sextet3, sextetAt } from "./group.ts";

/** The first `g` groups of three bytes are encoded: unit `4h + r` is sextet `r` of group `h`. */
export function encodedGroups(out: readonly nat[], bytes: readonly int[], g: nat): boolean {
  return forall((h: nat, r: nat) =>
    implies(
      h < g && r < 4 && 4 * h + r < out.length && 3 * h + 2 < bytes.length,
      out[4 * h + r] === encodeUnit(sextetAt(bytes[3 * h] & 0xff, bytes[3 * h + 1] & 0xff, bytes[3 * h + 2] & 0xff, r)),
    ),
  );
}

/** The encoded length of `bytes`: four characters per group of up to three. */
export function expectedLength(bytes: readonly int[]): nat {
  return Math.floor((bytes.length + 2) / 3) * 4;
}

export function holdsEncoded(out: readonly nat[], bytes: readonly int[]): boolean {
  return out.length >= Math.floor((bytes.length + 2) / 3) * 4;
}

/** `groups` is the number of whole groups of three in `n` bytes. */
export function wholeGroupsOf(groups: nat, n: nat): boolean {
  return groups === Math.floor(n / 3);
}

export function isLength(n: nat, bytes: readonly int[]): boolean {
  return n === bytes.length;
}

export function multipleOf4(i: nat): boolean {
  return i % 4 === 0;
}

/**
 * base64-js's `fromByteArray`, writing UTF-16 code units into `out` (at least
 * `expectedLength(bytes)` long). Each element is taken modulo 256 (`& 0xFF`), as base64-js
 * does for whole groups.
 */
export function encodeInto(bytes: readonly int[], out: nat[] & Is<typeof holdsEncoded, [typeof bytes]>): void & Modifies<typeof out> {
  encodeGroups(bytes, out);
  encodeTail(bytes, out);
}

/** In-place writes keep an array's length. */
export function sameSize(a: readonly nat[], b: readonly nat[]): boolean {
  return a.length === b.length;
}

/** Every whole group of three bytes is encoded. */
export function encodedWholeGroups(out: readonly nat[], bytes: readonly int[]): boolean {
  return encodedGroups(out, bytes, Math.floor(bytes.length / 3));
}

/** The whole groups: four units per three bytes. */
export function encodeGroups(
  bytes: readonly int[],
  out: nat[] & Is<typeof holdsEncoded, [typeof bytes]>,
):
  & void
  & Modifies<typeof out>
  & Holds<typeof encodedWholeGroups, [typeof out, typeof bytes]>
  & Holds<typeof holdsEncoded, [typeof out, typeof bytes]>
  & Holds<typeof sameSize, [typeof out, Old<typeof out>]> {
  const n = bytes.length;
  const groups = Math.floor(n / 3);
  let g = 0;
  while (g < groups) {
    g satisfies Le<typeof groups>;
    groups satisfies Is<typeof wholeGroupsOf, [typeof n]>;
    n satisfies Is<typeof isLength, [typeof bytes]>;
    out satisfies Is<typeof holdsEncoded, [typeof bytes]>;
    out satisfies Holds<typeof encodedGroups, [typeof out, typeof bytes, typeof g]>;
    out satisfies Holds<typeof sameSize, [typeof out, Old<typeof out>]>;
    groups - g satisfies Decreases;
    const a = bytes[3 * g] & 0xff;
    const b = bytes[3 * g + 1] & 0xff;
    const c = bytes[3 * g + 2] & 0xff;
    out[4 * g] = encodeUnit(sextet0(a));
    out[4 * g + 1] = encodeUnit(sextet1(a, b));
    out[4 * g + 2] = encodeUnit(sextet2(b, c));
    out[4 * g + 3] = encodeUnit(sextet3(c));
    g = g + 1;
  }
}

/** The last, incomplete group (one or two bytes), padded with `=`. */
export function encodeTail(bytes: readonly int[], out: nat[] & Is<typeof holdsEncoded, [typeof bytes]>): void & Modifies<typeof out> {
  const n = bytes.length;
  const groups = Math.floor(n / 3);
  const j = 4 * groups;
  const full = 3 * groups;
  if (n - full === 1) {
    const a = bytes[full] & 0xff;
    out[j] = encodeUnit(sextet0(a));
    out[j + 1] = encodeUnit(sextet1(a, 0));
    out[j + 2] = 61;
    out[j + 3] = 61;
  } else if (n - full === 2) {
    const a = bytes[full] & 0xff;
    const b = bytes[full + 1] & 0xff;
    out[j] = encodeUnit(sextet0(a));
    out[j + 1] = encodeUnit(sextet1(a, b));
    out[j + 2] = encodeUnit(sextet2(b, 0));
    out[j + 3] = 61;
  }
}

/** The position of the first `=` (or the length), as base64-js's `getLens`. */
export function validLength(s: string): nat & Le<typeof s.length> {
  let i = 0;
  while (i < s.length) {
    i satisfies Le<typeof s.length>;
    s.length - i satisfies Decreases;
    if (s.charCodeAt(i) === 61) return i;
    i = i + 1;
  }
  return i;
}

export function hasLengthMultipleOf4(s: string): boolean {
  return s.length % 4 === 0;
}

/** Padding characters base64-js assumes: 0 when there is no `=`, else `4 - valid % 4` (1 to 4). */
export function padding(s: string): nat {
  const valid = validLength(s);
  return valid === s.length ? 0 : 4 - (valid % 4);
}

/** base64-js's `byteLength` (negative for strings starting with `=`, where base64-js throws). */
export function byteLength(s: string): int {
  const valid = validLength(s);
  const pad = padding(s);
  const q = Math.floor(((valid + pad) * 3) / 4);
  const qi: int = q;
  return qi - pad;
}

/** Where base64-js's main loop stops: the end of the last complete group it decodes. */
export function groupsEnd(s: string): nat & Le<typeof s.length> & Is<typeof multipleOf4> {
  const valid = validLength(s);
  const pad = valid === s.length ? 0 : 4 - (valid % 4);
  if (pad === 0) return valid - (valid % 4);
  if (pad === 4) return valid >= 4 ? valid - 4 : 0;
  return valid - (valid % 4);
}

/** Bytes decoded from the padded last group. */
export function tailBytes(pad: nat): nat {
  return pad === 2 ? 1 : pad === 1 ? 2 : 0;
}

/** `out` can hold what decoding `s` writes. */
export function holdsDecoded(out: readonly nat[], s: string): boolean {
  return out.length >= Math.floor(groupsEnd(s) / 4) * 3 + tailBytes(padding(s));
}

export function threeQuarters(k: nat, i: nat): boolean {
  return i % 4 === 0 && k % 3 === 0 && Math.floor(k / 3) === Math.floor(i / 4);
}

export function isGroupsEnd(e: nat, s: string): boolean {
  return e === groupsEnd(s);
}

export function isPadding(p: nat, s: string): boolean {
  return p === padding(s);
}

/** `count` is the number of complete groups base64-js decodes in its main loop. */
export function isGroupCount(count: nat, s: string): boolean {
  return count === Math.floor(groupsEnd(s) / 4);
}

/** `count` groups of four characters fit in `s`. */
export function fitsIn(count: nat, s: string): boolean {
  return count <= Math.floor(s.length / 4);
}

/** The first `g` groups of four characters are decoded: bytes `3h` to `3h + 2` from group `h`. */
export function decodedGroups(out: readonly nat[], s: string, g: nat): boolean {
  return forall((h: nat) =>
    implies(
      h < g && 3 * h + 2 < out.length && 4 * h + 3 < s.length,
      out[3 * h] === byte0(decodeUnit(s.charCodeAt(4 * h)), decodeUnit(s.charCodeAt(4 * h + 1))) &&
        out[3 * h + 1] === byte1(decodeUnit(s.charCodeAt(4 * h + 1)), decodeUnit(s.charCodeAt(4 * h + 2))) &&
        out[3 * h + 2] === byte2(decodeUnit(s.charCodeAt(4 * h + 2)), decodeUnit(s.charCodeAt(4 * h + 3))),
    ),
  );
}

/**
 * base64-js's `toByteArray`, writing into `out` (at least `written(s)` long): in place, so
 * that a `Uint8Array` is filled without copies. Bytes not written keep their value.
 */
export function decodeInto(s: string & Is<typeof hasLengthMultipleOf4>, out: nat[] & Is<typeof holdsDecoded, [typeof s]>): void & Modifies<typeof out> {
  const end = groupsEnd(s);
  const count = Math.floor(end / 4);
  decodeGroups(s, out, count);
  decodeTail(s, out, count);
}

/** The complete groups: three bytes per four characters. */
export function decodeGroups(
  s: string,
  out: nat[] & Is<typeof holdsDecoded, [typeof s]>,
  count: nat & Is<typeof isGroupCount, [typeof s]> & Is<typeof fitsIn, [typeof s]>,
):
  & void
  & Modifies<typeof out>
  & Holds<typeof decodedGroups, [typeof out, typeof s, typeof count]>
  & Holds<typeof holdsDecoded, [typeof out, typeof s]>
  & Holds<typeof sameSize, [typeof out, Old<typeof out>]> {
  let h = 0;
  while (h < count) {
    h satisfies Le<typeof count>;
    count satisfies Is<typeof isGroupCount, [typeof s]> & Is<typeof fitsIn, [typeof s]>;
    out satisfies Is<typeof holdsDecoded, [typeof s]>;
    out satisfies Holds<typeof decodedGroups, [typeof out, typeof s, typeof h]>;
    out satisfies Holds<typeof sameSize, [typeof out, Old<typeof out>]>;
    count - h satisfies Decreases;
    const s0 = decodeUnit(s.charCodeAt(4 * h));
    const s1 = decodeUnit(s.charCodeAt(4 * h + 1));
    const s2 = decodeUnit(s.charCodeAt(4 * h + 2));
    const s3 = decodeUnit(s.charCodeAt(4 * h + 3));
    out[3 * h] = byte0(s0, s1);
    out[3 * h + 1] = byte1(s1, s2);
    out[3 * h + 2] = byte2(s2, s3);
    h = h + 1;
  }
}

/**
 * The padded last group. base64-js reads it where its main loop stops; its characters are
 * always there, and the bytes fit (the checks never fail). Were a check to fail, base64-js
 * would read NaN, decode 0 and write the 0 that `out` already holds.
 */
export function decodeTail(s: string, out: nat[], count: nat): void & Modifies<typeof out> {
  const pad = padding(s);
  if (count > 2251799813685247) return;
  const i = 4 * count;
  const k = 3 * count;
  if (pad === 2 && s.length >= 2) {
    if (i <= s.length - 2 && k < out.length) {
      const s0 = decodeUnit(s.charCodeAt(i));
      const s1 = decodeUnit(s.charCodeAt(i + 1));
      out[k] = byte0(s0, s1);
    }
  } else if (pad === 1 && s.length >= 3 && out.length >= 2) {
    if (i <= s.length - 3 && k <= out.length - 2) {
      const s0 = decodeUnit(s.charCodeAt(i));
      const s1 = decodeUnit(s.charCodeAt(i + 1));
      const s2 = decodeUnit(s.charCodeAt(i + 2));
      out[k] = byte0(s0, s1);
      out[k + 1] = byte1(s1, s2);
    }
  }
}
