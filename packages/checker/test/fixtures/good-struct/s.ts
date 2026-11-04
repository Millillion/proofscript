import { by, cases, eq, prove, rfl, simp, type nat, type Proof } from "proofscript";

// A plain object type (no `tag`) is a structure in the logic.
export type Point = { readonly x: nat; readonly y: nat };

// Interfaces work too.
export interface Range {
  readonly lo: nat;
  readonly hi: nat;
}

export function swap(p: Point): Point {
  return { x: p.y, y: p.x };
}

export function isEmpty(r: Range): boolean {
  return r.hi <= r.lo;
}

export function swap_swap(p: Point): Proof {
  return prove(eq(swap(swap(p)), p), by(cases(p), rfl));
}

export function empty_when_equal(n: nat): Proof {
  return prove(isEmpty({ lo: n, hi: n }), by(simp(isEmpty)));
}
