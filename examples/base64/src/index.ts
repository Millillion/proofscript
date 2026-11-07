// base64-js's API (`byteLength`, `toByteArray`, `fromByteArray`) over the verified core in
// base64.ts. This file is the boundary: it allocates buffers and converts types, and is not
// itself verified (`proofscript audit` lists its calls).
import type { int, nat } from "proofscript";
import { byteLength as coreByteLength, decodeInto, encodeInto, expectedLength } from "./base64.ts";

function checkLength(b64: string): void {
  if (b64.length % 4 > 0) throw new Error("Invalid string. Length must be a multiple of 4");
}

/** The number of bytes `toByteArray(b64)` returns. */
export function byteLength(b64: string): number {
  checkLength(b64);
  return coreByteLength(b64);
}

/** Decodes base64 (and URL-safe base64) into bytes. */
export function toByteArray(b64: string): Uint8Array {
  checkLength(b64);
  // As in base64-js, a negative length (a string starting with `=`) throws a RangeError here.
  const out = new Uint8Array(coreByteLength(b64));
  // A Uint8Array is indexed and assigned like an array of numbers below 256.
  decodeInto(b64, out as unknown as nat[]);
  return out;
}

/** Encodes bytes as base64. */
export function fromByteArray(uint8: Uint8Array | ArrayLike<number>): string {
  const bytes = uint8 as unknown as readonly int[];
  const out = new Uint8Array(expectedLength(bytes));
  encodeInto(bytes, out as unknown as nat[]);
  // Every unit is an ASCII code (below 128), where latin1 is the identity.
  return new TextDecoder("latin1").decode(out);
}
