import type { Modifies, nat } from "proofscript";

// Writes past the end (JavaScript would grow the array with a hole): rejected.
export function append(a: nat[]): void & Modifies<typeof a> {
  a[a.length] = 1;
}
