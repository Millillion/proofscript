import type { Decreases, Holds, Is, Le, Lt, Modifies, Old, nat } from "proofscript";

export function swapped(b: readonly nat[], a: readonly nat[], i: nat, j: nat): boolean {
  if (i < a.length && j < a.length && b.length === a.length) return b[i] === a[j] && b[j] === a[i];
  return false;
}

// Swap two elements in place. `Modifies` declares the change; the postcondition
// relates the array after the call (`typeof a`) to the array before it (`Old<typeof a>`).
export function swapAt(
  a: nat[],
  i: nat & Lt<typeof a.length>,
  j: nat & Lt<typeof a.length>,
): void & Modifies<typeof a> & Holds<typeof swapped, [typeof a, Old<typeof a>, typeof i, typeof j]> {
  const t = a[i];
  a[i] = a[j];
  a[j] = t;
}

export function hasLength(out: readonly nat[], n: nat): boolean {
  return out.length === n;
}

// Building a new array with push.
export function copy(a: readonly nat[]): nat[] & Is<typeof hasLength, [typeof a.length]> {
  const out: nat[] = [];
  for (let i = 0; i < a.length; i++) {
    i satisfies Le<typeof a.length>;
    out satisfies Is<typeof hasLength, [typeof i]>;
    a.length - i satisfies Decreases;
    out.push(a[i]);
  }
  return out;
}

// A mutable object field.
export type Counter = { count: nat };

export function grew(n: Counter, o: Counter): boolean {
  return n.count > o.count;
}

export function small(c: Counter): boolean {
  return c.count < 1000;
}

export function bump(c: Counter & Is<typeof small>): void & Modifies<typeof c> & Holds<typeof grew, [typeof c, Old<typeof c>]> {
  c.count = c.count + 1;
}

// A caller: the call rebinds `a` to its new value.
export function swapFirstTwo(a: nat[] & Is<typeof longEnough>): void & Modifies<typeof a> {
  swapAt(a, 0, 1);
}

export function longEnough(a: readonly nat[]): boolean {
  return a.length >= 2;
}
