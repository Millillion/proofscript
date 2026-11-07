// The bit arithmetic of one group: three bytes are four sextets. Encoding and decoding use
// exactly these functions, so the theorems below are about the code that runs.
import { by, implies, intro, omega, prove, unfold, type Lt, type nat, type Proof } from "proofscript";


export function sextet0(a: nat & Lt<256>): nat & Lt<64> {
  return a >> 2;
}
export function sextet1(a: nat & Lt<256>, b: nat & Lt<256>): nat & Lt<64> {
  return ((a & 3) << 4) + (b >> 4);
}
export function sextet2(b: nat & Lt<256>, c: nat & Lt<256>): nat & Lt<64> {
  return ((b & 15) << 2) + (c >> 6);
}
export function sextet3(c: nat & Lt<256>): nat & Lt<64> {
  return c & 63;
}

export function byte0(x0: nat & Lt<64>, x1: nat & Lt<64>): nat & Lt<256> {
  return (x0 << 2) + (x1 >> 4);
}
export function byte1(x1: nat & Lt<64>, x2: nat & Lt<64>): nat & Lt<256> {
  return ((x1 & 15) << 4) + (x2 >> 2);
}
export function byte2(x2: nat & Lt<64>, x3: nat & Lt<64>): nat & Lt<256> {
  return ((x2 & 3) << 6) + x3;
}

/** Decoding a group's sextets gives back its bytes. */
export function group_round_trip(a: nat, b: nat, c: nat): Proof {
  return prove(
    implies(
      a < 256 && b < 256 && c < 256,
      byte0(sextet0(a), sextet1(a, b)) === a && byte1(sextet1(a, b), sextet2(b, c)) === b && byte2(sextet2(b, c), sextet3(c)) === c,
    ),
    by(intro("h"), unfold(byte0, byte1, byte2, sextet0, sextet1, sextet2, sextet3), omega),
  );
}

/** A padded group of two bytes (its third byte encoded as 0) decodes to them. */
export function pair_round_trip(a: nat, b: nat): Proof {
  return prove(implies(a < 256 && b < 256, byte0(sextet0(a), sextet1(a, b)) === a && byte1(sextet1(a, b), sextet2(b, 0)) === b), by(intro("h"), unfold(byte0, byte1, sextet0, sextet1, sextet2), omega));
}

/** A padded group of one byte decodes to it. */
export function single_round_trip(a: nat): Proof {
  return prove(implies(a < 256, byte0(sextet0(a), sextet1(a, 0)) === a), by(intro("h"), unfold(byte0, sextet0, sextet1), omega));
}

/** The `r`-th sextet of the group `a, b, c`. */
export function sextetAt(a: nat & Lt<256>, b: nat & Lt<256>, c: nat & Lt<256>, r: nat & Lt<4>): nat & Lt<64> {
  if (r === 0) return sextet0(a);
  if (r === 1) return sextet1(a, b);
  if (r === 2) return sextet2(b, c);
  return sextet3(c);
}
