const BASE64_ALPHABET =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

const lookup = [...BASE64_ALPHABET];
const revLookup: number[] = [];

for (let index = 0; index < BASE64_ALPHABET.length; index += 1) {
  revLookup[BASE64_ALPHABET.charCodeAt(index)] = index;
}
revLookup["-".charCodeAt(0)] = 62;
revLookup["_".charCodeAt(0)] = 63;

export type Byte = number;
export type Sextet = number;
export type CodeUnit = number;
export type CodeUnitString = string;
export type ByteArray = ReadonlyArray<number>;

function floorDiv(value: number, divisor: number): number {
  return Math.floor(value / divisor);
}

function normalizeByte(value: number): number {
  return value & 0xff;
}

function packTriplet(b0: number, b1: number, b2: number): number {
  return (
    ((normalizeByte(b0) << 16) & 0xff0000) +
    ((normalizeByte(b1) << 8) & 0xff00) +
    (normalizeByte(b2) & 0xff)
  );
}

export function sextetAtSpec(index: Sextet): string {
  return BASE64_ALPHABET[index] as unknown as string;
}

export function sextetAt(index: Sextet): string {
  return lookup[index] as unknown as string;
}

export function tripletToBase64Spec(num: number): string {
  return (
    sextetAtSpec((num >> 18) & 0x3f) +
    sextetAtSpec((num >> 12) & 0x3f) +
    sextetAtSpec((num >> 6) & 0x3f) +
    sextetAtSpec(num & 0x3f)
  );
}

export function tripletToBase64(num: number): string {
  return (
    sextetAt((num >> 18) & 0x3f) +
    sextetAt((num >> 12) & 0x3f) +
    sextetAt((num >> 6) & 0x3f) +
    sextetAt(num & 0x3f)
  );
}

export function tripletBytesToBase64Spec(b0: Byte, b1: Byte, b2: Byte): string {
  const n0 = normalizeByte(b0);
  const n1 = normalizeByte(b1);
  const n2 = normalizeByte(b2);
  const s0 = floorDiv(n0, 4);
  const s1 = ((n0 % 4) * 16) + floorDiv(n1, 16);
  const s2 = ((n1 % 16) * 4) + floorDiv(n2, 64);
  const s3 = n2 % 64;
  return sextetAtSpec(s0) + sextetAtSpec(s1) + sextetAtSpec(s2) + sextetAtSpec(s3);
}

export function tripletBytesToBase64(b0: Byte, b1: Byte, b2: Byte): string {
  return tripletToBase64(packTriplet(b0, b1, b2));
}

export function singleByteToBase64Spec(b0: Byte): string {
  const n0 = normalizeByte(b0);
  return sextetAtSpec(floorDiv(n0, 4)) + sextetAtSpec((n0 % 4) * 16) + "==";
}

export function singleByteToBase64(b0: Byte): string {
  const tmp = b0;
  return sextetAt(tmp >> 2) + sextetAt((tmp << 4) & 0x3f) + "==";
}

export function doubleByteToBase64Spec(b0: Byte, b1: Byte): string {
  const n0 = normalizeByte(b0);
  const n1 = normalizeByte(b1);
  const s0 = floorDiv(n0, 4);
  const s1 = ((n0 % 4) * 16) + floorDiv(n1, 16);
  const s2 = (n1 % 16) * 4;
  return sextetAtSpec(s0) + sextetAtSpec(s1) + sextetAtSpec(s2) + "=";
}

export function doubleByteToBase64(b0: Byte, b1: Byte): string {
  const tmp = (b0 << 8) + b1;
  return sextetAt(tmp >> 10) + sextetAt((tmp >> 4) & 0x3f) + sextetAt((tmp << 2) & 0x3f) + "=";
}

export function encodeChunkSpec(uint8: ByteArray, start: number, end: number): string {
  let tmp = 0;
  const output: string[] = [];
  for (let i = start; i < end; i += 3) {
    proofscriptInvariant(start <= i && i <= end);
    proofscriptInvariant((i - start) % 3 === 0);
    proofscriptDecreases(end - i);
    tmp = packTriplet(uint8[i], uint8[i + 1], uint8[i + 2]);
    output.push(tripletBytesToBase64Spec(uint8[i], uint8[i + 1], uint8[i + 2]));
  }
  return output.join("");
}

export function encodeChunk(uint8: ByteArray, start: number, end: number): string {
  let tmp = 0;
  const output: string[] = [];
  for (let i = start; i < end; i += 3) {
    proofscriptInvariant(start <= i && i <= end);
    proofscriptInvariant((i - start) % 3 === 0);
    proofscriptDecreases(end - i);
    tmp = packTriplet(uint8[i], uint8[i + 1], uint8[i + 2]);
    output.push(tripletBytesToBase64(uint8[i], uint8[i + 1], uint8[i + 2]));
  }
  return output.join("");
}

export function fromByteArraySpec(uint8: ByteArray): string {
  let tmp = 0;
  const len = uint8.length;
  const extraBytes = len % 3;
  const parts: string[] = [];
  const maxChunkLength = 16383;
  for (let i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    proofscriptInvariant(0 <= i && i <= len2);
    proofscriptDecreases(len2 - i);
    parts.push(encodeChunkSpec(uint8, i, (i + maxChunkLength) > len2 ? len2 : (i + maxChunkLength)));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    parts.push(singleByteToBase64Spec(tmp));
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    parts.push(doubleByteToBase64Spec(uint8[len - 2], uint8[len - 1]));
  }
  return parts.join("");
}

export function fromByteArray(uint8: ByteArray): string {
  let tmp = 0;
  const len = uint8.length;
  const extraBytes = len % 3;
  const parts: string[] = [];
  const maxChunkLength = 16383;
  for (let i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    proofscriptInvariant(0 <= i && i <= len2);
    proofscriptDecreases(len2 - i);
    parts.push(encodeChunk(uint8, i, (i + maxChunkLength) > len2 ? len2 : (i + maxChunkLength)));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    parts.push(singleByteToBase64(tmp));
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    parts.push(doubleByteToBase64(uint8[len - 2], uint8[len - 1]));
  }
  return parts.join("");
}

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

export function decodeTail2Spec(s0: Sextet, s1: Sextet): number[] {
  return [s0 * 4 + floorDiv(s1, 16)];
}

export function decodeTail2(s0: Sextet, s1: Sextet): number[] {
  return [((s0 << 2) | (s1 >> 4)) & 0xff];
}

export function decodeTail3Spec(s0: Sextet, s1: Sextet, s2: Sextet): number[] {
  return [s0 * 4 + floorDiv(s1, 16), ((s1 % 16) * 16) + floorDiv(s2, 4)];
}

export function decodeTail3(s0: Sextet, s1: Sextet, s2: Sextet): number[] {
  return [((s0 << 2) | (s1 >> 4)) & 0xff, (((s1 & 0x0f) << 4) | (s2 >> 2)) & 0xff];
}

export function decodeQuartetSpec(s0: Sextet, s1: Sextet, s2: Sextet, s3: Sextet): number[] {
  return [
    s0 * 4 + floorDiv(s1, 16),
    ((s1 % 16) * 16) + floorDiv(s2, 4),
    ((s2 % 4) * 64) + s3,
  ];
}

export function decodeQuartet(s0: Sextet, s1: Sextet, s2: Sextet, s3: Sextet): number[] {
  const tmp = (s0 << 18) | (s1 << 12) | (s2 << 6) | s3;
  return [(tmp >> 16) & 0xff, (tmp >> 8) & 0xff, tmp & 0xff];
}

export function advancePaddingIndexSpec(value: number): number {
  if (value === -1) {
    return -1;
  }
  return value + 1;
}

export function advancePaddingIndex(value: number): number {
  if (value === -1) {
    return -1;
  }
  return value + 1;
}

export function firstPaddingIndexFromSpec(text: string, index: number): number {
  if (index === text.length) {
    return -1;
  }
  if (text[index] === "=") {
    return 0;
  }
  return advancePaddingIndexSpec(firstPaddingIndexFromSpec(text, index + 1));
}

export function firstPaddingIndexFrom(text: string, index: number): number {
  if (index === text.length) {
    return -1;
  }
  if (text[index] === "=") {
    return 0;
  }
  return advancePaddingIndex(firstPaddingIndexFrom(text, index + 1));
}

export function firstPaddingIndexSpec(text: string): number {
  return firstPaddingIndexFromSpec(text, 0);
}

export function firstPaddingIndex(text: string): number {
  return firstPaddingIndexFrom(text, 0);
}

export function getLensSpec(b64: string): [number, number] {
  const len = b64.length;

  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }

  let validLen = firstPaddingIndexSpec(b64);
  if (validLen === -1) {
    validLen = len;
  }

  const placeHoldersLen = validLen === len ? 0 : 4 - (validLen % 4);
  return [validLen, placeHoldersLen];
}

export function getLens(b64: string): [number, number] {
  const len = b64.length;

  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }

  let validLen = firstPaddingIndex(b64);
  if (validLen === -1) {
    validLen = len;
  }

  const placeHoldersLen = validLen === len ? 0 : 4 - (validLen % 4);
  return [validLen, placeHoldersLen];
}

export function _byteLengthSpec(b64: string, validLen: number, placeHoldersLen: number): number {
  return (((validLen + placeHoldersLen) * 3) / 4) - placeHoldersLen;
}

export function _byteLength(b64: string, validLen: number, placeHoldersLen: number): number {
  return (((validLen + placeHoldersLen) * 3) / 4) - placeHoldersLen;
}

export function byteLengthSpec(b64: string): number {
  const lens = getLensSpec(b64);
  const validLen = lens[0];
  const placeHoldersLen = lens[1];
  return _byteLengthSpec(b64, validLen, placeHoldersLen);
}

export function byteLength(b64: string): number {
  const lens = getLens(b64);
  const validLen = lens[0];
  const placeHoldersLen = lens[1];
  return _byteLength(b64, validLen, placeHoldersLen);
}

export function toByteArraySpec(b64: string): Uint8Array {
  let tmp = 0;
  const lens = getLensSpec(b64);
  const validLen = lens[0];
  const placeHoldersLen = lens[1];
  const arr = new Uint8Array(_byteLengthSpec(b64, validLen, placeHoldersLen));
  let curByte = 0;
  const len = placeHoldersLen > 0 ? validLen - 4 : validLen;
  let i = 0;
  for (i = 0; i < len; i += 4) {
    proofscriptInvariant(0 <= i && i <= len);
    proofscriptInvariant(0 <= curByte && curByte <= arr.length);
    proofscriptDecreases(len - i);
    tmp =
      (charToSextetSpec(b64[i]) << 18) |
      (charToSextetSpec(b64[i + 1]) << 12) |
      (charToSextetSpec(b64[i + 2]) << 6) |
      charToSextetSpec(b64[i + 3]);
    arr[curByte++] = (tmp >> 16) & 0xff;
    arr[curByte++] = (tmp >> 8) & 0xff;
    arr[curByte++] = tmp & 0xff;
  }
  if (placeHoldersLen === 2) {
    tmp = (charToSextetSpec(b64[i]) << 2) | (charToSextetSpec(b64[i + 1]) >> 4);
    arr[curByte++] = tmp & 0xff;
  }
  if (placeHoldersLen === 1) {
    tmp =
      (charToSextetSpec(b64[i]) << 10) |
      (charToSextetSpec(b64[i + 1]) << 4) |
      (charToSextetSpec(b64[i + 2]) >> 2);
    arr[curByte++] = (tmp >> 8) & 0xff;
    arr[curByte++] = tmp & 0xff;
  }
  return arr;
}

export function toByteArray(b64: string): Uint8Array {
  let tmp = 0;
  const lens = getLens(b64);
  const validLen = lens[0];
  const placeHoldersLen = lens[1];
  const arr = new Uint8Array(_byteLength(b64, validLen, placeHoldersLen));
  let curByte = 0;
  const len = placeHoldersLen > 0 ? validLen - 4 : validLen;
  let i = 0;
  for (i = 0; i < len; i += 4) {
    proofscriptInvariant(0 <= i && i <= len);
    proofscriptInvariant(0 <= curByte && curByte <= arr.length);
    proofscriptDecreases(len - i);
    tmp =
      (charToSextet(b64[i]) << 18) |
      (charToSextet(b64[i + 1]) << 12) |
      (charToSextet(b64[i + 2]) << 6) |
      charToSextet(b64[i + 3]);
    arr[curByte++] = (tmp >> 16) & 0xff;
    arr[curByte++] = (tmp >> 8) & 0xff;
    arr[curByte++] = tmp & 0xff;
  }
  if (placeHoldersLen === 2) {
    tmp = (charToSextet(b64[i]) << 2) | (charToSextet(b64[i + 1]) >> 4);
    arr[curByte++] = tmp & 0xff;
  }
  if (placeHoldersLen === 1) {
    tmp =
      (charToSextet(b64[i]) << 10) |
      (charToSextet(b64[i + 1]) << 4) |
      (charToSextet(b64[i + 2]) >> 2);
    arr[curByte++] = (tmp >> 8) & 0xff;
    arr[curByte++] = tmp & 0xff;
  }
  return arr;
}

declare const sextetAtSpecProof: ProofScriptSpec<typeof sextetAtSpec>;
declare const sextetAtProof: ProofScriptImpl<typeof sextetAt, typeof sextetAtSpec>;
declare const tripletToBase64SpecProof: ProofScriptSpec<typeof tripletToBase64Spec>;
declare const tripletToBase64Proof: ProofScriptImpl<typeof tripletToBase64, typeof tripletToBase64Spec>;
declare const tripletBytesToBase64SpecProof: ProofScriptSpec<typeof tripletBytesToBase64Spec>;
declare const tripletBytesToBase64Proof: ProofScriptImpl<
  typeof tripletBytesToBase64,
  typeof tripletBytesToBase64Spec
>;
declare const singleByteToBase64SpecProof: ProofScriptSpec<typeof singleByteToBase64Spec>;
declare const singleByteToBase64Proof: ProofScriptImpl<typeof singleByteToBase64, typeof singleByteToBase64Spec>;
declare const doubleByteToBase64SpecProof: ProofScriptSpec<typeof doubleByteToBase64Spec>;
declare const doubleByteToBase64Proof: ProofScriptImpl<typeof doubleByteToBase64, typeof doubleByteToBase64Spec>;
declare const encodeChunkSpecProof: ProofScriptSpec<typeof encodeChunkSpec>;
declare const encodeChunkProof: ProofScriptImpl<typeof encodeChunk, typeof encodeChunkSpec>;
declare const fromByteArraySpecProof: ProofScriptSpec<typeof fromByteArraySpec>;
declare const fromByteArrayProof: ProofScriptImpl<typeof fromByteArray, typeof fromByteArraySpec>;
declare const charToSextetSpecProof: ProofScriptSpec<typeof charToSextetSpec>;
declare const charToSextetProof: ProofScriptImpl<typeof charToSextet, typeof charToSextetSpec>;
declare const decodeTail2SpecProof: ProofScriptSpec<typeof decodeTail2Spec>;
declare const decodeTail2Proof: ProofScriptImpl<typeof decodeTail2, typeof decodeTail2Spec>;
declare const decodeTail3SpecProof: ProofScriptSpec<typeof decodeTail3Spec>;
declare const decodeTail3Proof: ProofScriptImpl<typeof decodeTail3, typeof decodeTail3Spec>;
declare const decodeQuartetSpecProof: ProofScriptSpec<typeof decodeQuartetSpec>;
declare const decodeQuartetProof: ProofScriptImpl<typeof decodeQuartet, typeof decodeQuartetSpec>;
declare const advancePaddingIndexSpecProof: ProofScriptSpec<typeof advancePaddingIndexSpec>;
declare const advancePaddingIndexProof: ProofScriptImpl<typeof advancePaddingIndex, typeof advancePaddingIndexSpec>;
declare const firstPaddingIndexFromSpecProof: ProofScriptSpec<typeof firstPaddingIndexFromSpec>;
declare const firstPaddingIndexFromProof: ProofScriptImpl<
  typeof firstPaddingIndexFrom,
  typeof firstPaddingIndexFromSpec
>;
declare const firstPaddingIndexSpecProof: ProofScriptSpec<typeof firstPaddingIndexSpec>;
declare const firstPaddingIndexProof: ProofScriptImpl<typeof firstPaddingIndex, typeof firstPaddingIndexSpec>;
declare const getLensSpecProof: ProofScriptSpec<typeof getLensSpec>;
declare const getLensProof: ProofScriptImpl<typeof getLens, typeof getLensSpec>;
declare const _byteLengthSpecProof: ProofScriptSpec<typeof _byteLengthSpec>;
declare const _byteLengthProof: ProofScriptImpl<typeof _byteLength, typeof _byteLengthSpec>;
declare const byteLengthSpecProof: ProofScriptSpec<typeof byteLengthSpec>;
declare const byteLengthProof: ProofScriptImpl<typeof byteLength, typeof byteLengthSpec>;
declare const toByteArraySpecProof: ProofScriptSpec<typeof toByteArraySpec>;
declare const toByteArrayProof: ProofScriptImpl<typeof toByteArray, typeof toByteArraySpec>;
