// The round trip for one group: decoding the units the encoder writes gives back the bytes.
import { by, grind, implies, intro, prove, unfold, type nat, type Proof } from "proofscript";
import { decode_encode_unit, decodeUnit, encodeUnit } from "./alphabet.ts";
import { byte0, byte1, byte2, group_round_trip, sextetAt } from "./group.ts";

/** The units `encodeGroups` writes for bytes `a`, `b`, `c` decode, by `decodeGroups`, to `a`, `b`, `c`. */
export function group_decodes(a: nat, b: nat, c: nat): Proof {
  return prove(
    implies(
      a < 256 && b < 256 && c < 256,
      byte0(decodeUnit(encodeUnit(sextetAt(a, b, c, 0))), decodeUnit(encodeUnit(sextetAt(a, b, c, 1)))) === a &&
        byte1(decodeUnit(encodeUnit(sextetAt(a, b, c, 1))), decodeUnit(encodeUnit(sextetAt(a, b, c, 2)))) === b &&
        byte2(decodeUnit(encodeUnit(sextetAt(a, b, c, 2))), decodeUnit(encodeUnit(sextetAt(a, b, c, 3)))) === c,
    ),
    by(intro("h"), unfold(sextetAt), grind(decode_encode_unit, group_round_trip)),
  );
}
