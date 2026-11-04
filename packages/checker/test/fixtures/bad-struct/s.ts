import { by, cases, eq, prove, rfl, type nat, type Proof } from "proofscript";

export type Point = { readonly x: nat; readonly y: nat };

export function swap(p: Point): Point {
  return { x: p.y, y: p.x };
}

// False: swapping changes the point unless x === y. Must not verify.
export function swap_id(p: Point): Proof {
  return prove(eq(swap(p), p), by(cases(p), rfl));
}
