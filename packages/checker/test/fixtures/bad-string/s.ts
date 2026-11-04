import { decide, prove, type Proof } from "proofscript";

// False in JavaScript: "😀".length is 2. Must not verify.
export function emoji_is_one_unit(): Proof {
  return prove("😀".length === 1, decide);
}
