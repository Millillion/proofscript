// Base64 encoding and decoding with base64-js's behaviour, verified: every array access is
// in bounds, no arithmetic overflows, every output byte is a byte, and the output lengths
// are exact.
import type { Decreases, Is, Le, Modifies, int, nat } from "proofscript";
import { decodeUnit, encodeUnit } from "./alphabet.ts";
import { byte0, byte1, byte2, sextet0, sextet1, sextet2, sextet3 } from "./group.ts";

export function multipleOf3(i: nat): boolean {
  return i % 3 === 0;
}

/** `full` is `n` without its last incomplete group of three. */
export function wholeGroups(full: nat, n: nat): boolean {
  return full === n - (n % 3);
}

export function isLength(n: nat, bytes: readonly int[]): boolean {
  return n === bytes.length;
}

export function multipleOf4(i: nat): boolean {
  return i % 4 === 0;
}

/** The encoded length of `bytes`: four characters per group of up to three. */
export function expectedLength(bytes: readonly int[]): nat {
  return Math.floor((bytes.length + 2) / 3) * 4;
}

export function holdsEncoded(out: readonly nat[], bytes: readonly int[]): boolean {
  return out.length >= Math.floor((bytes.length + 2) / 3) * 4;
}

/** Where the `j`-th output unit of the `i`-th byte goes: four units per three bytes. */
export function unitsFor(j: nat, i: nat): boolean {
  return j % 4 === 0 && Math.floor(j / 4) === Math.floor(i / 3);
}

/**
 * base64-js's `fromByteArray`, writing UTF-16 code units into `out` (at least
 * `expectedLength(bytes)` long). Each element is taken modulo 256 (`& 0xFF`), as base64-js
 * does for whole groups.
 */
export function encodeInto(bytes: readonly int[], out: nat[] & Is<typeof holdsEncoded, [typeof bytes]>): void & Modifies<typeof out> {
  const n = bytes.length;
  const full = n - (n % 3);
  let i = 0;
  let j = 0;
  while (i < full) {
    i satisfies Le<typeof full> & Is<typeof multipleOf3>;
    full satisfies Is<typeof wholeGroups, [typeof n]>;
    n satisfies Is<typeof isLength, [typeof bytes]>;
    out satisfies Is<typeof holdsEncoded, [typeof bytes]>;
    j satisfies Is<typeof unitsFor, [typeof i]>;
    full - i satisfies Decreases;
    const a = bytes[i] & 0xff;
    const b = bytes[i + 1] & 0xff;
    const c = bytes[i + 2] & 0xff;
    out[j] = encodeUnit(sextet0(a));
    out[j + 1] = encodeUnit(sextet1(a, b));
    out[j + 2] = encodeUnit(sextet2(b, c));
    out[j + 3] = encodeUnit(sextet3(c));
    i = i + 3;
    j = j + 4;
  }
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

/**
 * base64-js's `toByteArray`, writing into `out` (at least `written(s)` long): in place, so
 * that a `Uint8Array` is filled without copies. Bytes not written keep their value.
 */
export function decodeInto(s: string & Is<typeof hasLengthMultipleOf4>, out: nat[] & Is<typeof holdsDecoded, [typeof s]>): void & Modifies<typeof out> {
  const end = groupsEnd(s);
  const pad = padding(s);
  let i = 0;
  let k = 0;
  while (i < end) {
    i satisfies Le<typeof end> & Is<typeof multipleOf4>;
    end satisfies Le<typeof s.length> & Is<typeof multipleOf4> & Is<typeof isGroupsEnd, [typeof s]>;
    pad satisfies Is<typeof isPadding, [typeof s]>;
    out satisfies Is<typeof holdsDecoded, [typeof s]>;
    k satisfies Is<typeof threeQuarters, [typeof i]>;
    end - i satisfies Decreases;
    const s0 = decodeUnit(s.charCodeAt(i));
    const s1 = decodeUnit(s.charCodeAt(i + 1));
    const s2 = decodeUnit(s.charCodeAt(i + 2));
    const s3 = decodeUnit(s.charCodeAt(i + 3));
    out[k] = byte0(s0, s1);
    out[k + 1] = byte1(s1, s2);
    out[k + 2] = byte2(s2, s3);
    i = i + 4;
    k = k + 3;
  }
  // The padded last group. base64-js reads it at the loop's end; its characters are always
  // there, and the bytes fit (the checks never fail). Were a check to fail, base64-js would
  // read NaN, decode 0 and write the 0 that `out` already holds.
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
