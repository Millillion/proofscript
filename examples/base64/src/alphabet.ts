// The base64 alphabet (RFC 4648), as arithmetic on UTF-16 code units.
import { decide, forall, implies, prove, type Lt, type nat, type Proof } from "proofscript";

/** Sextet → code unit: A–Z, a–z, 0–9, `+`, `/`. */
export function encodeUnit(v: nat & Lt<64>): nat & Lt<128> {
  if (v < 26) return 65 + v;
  if (v < 52) return 71 + v;
  if (v < 62) return v - 4;
  return v === 62 ? 43 : 47;
}

/**
 * Code unit → sextet. The URL-safe `-` and `_` decode as `+` and `/` (as in Node.js and
 * base64-js); any other character decodes as 0, as base64-js does.
 */
export function decodeUnit(c: nat): nat & Lt<64> {
  if (c >= 65 && c <= 90) return c - 65;
  if (c >= 97 && c <= 122) return c - 71;
  if (c >= 48 && c <= 57) return c + 4;
  if (c === 43 || c === 45) return 62;
  if (c === 47 || c === 95) return 63;
  return 0;
}

/** The alphabet never produces `=` (61), so padding is found where the encoder put it. */
export function encode_unit_not_padding(): Proof {
  return prove(forall((v: nat) => implies(v < 64, encodeUnit(v) !== 61)), decide);
}

/** Decoding inverts encoding, for every sextet (checked by evaluation, all 64 cases). */
export function decode_encode_unit(): Proof {
  return prove(forall((v: nat) => implies(v < 64, decodeUnit(encodeUnit(v)) === v)), decide);
}
