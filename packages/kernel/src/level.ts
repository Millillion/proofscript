// Universe levels and their decision procedures.
//
// `geq` is *complete*: it decides `l1 >= l2` for every assignment of natural
// numbers to the parameters. Lean's C++ kernel uses a sound but incomplete
// heuristic; we instead case-split each parameter that occurs in the second
// argument of an `imax` (zero vs. successor), after which `imax` disappears and
// levels are maxima of `param + k` / `k` terms, compared term by term.

import { type Name, nameToString } from "./name.ts";

export type Level = Zero | Succ | Max | IMax | Param;

export interface Zero {
  readonly kind: "zero";
  readonly hash: number;
}
export interface Succ {
  readonly kind: "succ";
  readonly of: Level;
  readonly hash: number;
  readonly hasParam: boolean;
}
export interface Max {
  readonly kind: "max";
  readonly lhs: Level;
  readonly rhs: Level;
  readonly hash: number;
  readonly hasParam: boolean;
}
export interface IMax {
  readonly kind: "imax";
  readonly lhs: Level;
  readonly rhs: Level;
  readonly hash: number;
  readonly hasParam: boolean;
}
export interface Param {
  readonly kind: "param";
  readonly name: Name;
  readonly hash: number;
}

const mix = (a: number, b: number): number => (Math.imul(a ^ (b + 0x9e3779b9), 0x85ebca6b) ^ (a >>> 13)) | 0;

export const zero: Zero = { kind: "zero", hash: 17 };

export function succ(of: Level): Level {
  return { kind: "succ", of, hash: mix(31, of.hash), hasParam: hasParam(of) };
}
export function max(lhs: Level, rhs: Level): Level {
  return { kind: "max", lhs, rhs, hash: mix(mix(37, lhs.hash), rhs.hash), hasParam: hasParam(lhs) || hasParam(rhs) };
}
export function imax(lhs: Level, rhs: Level): Level {
  return { kind: "imax", lhs, rhs, hash: mix(mix(41, lhs.hash), rhs.hash), hasParam: hasParam(lhs) || hasParam(rhs) };
}
export function param(name: Name): Level {
  return { kind: "param", name, hash: mix(43, name.id) };
}

export function hasParam(l: Level): boolean {
  switch (l.kind) {
    case "zero":
      return false;
    case "param":
      return true;
    default:
      return l.hasParam;
  }
}

export function levelEqStructural(a: Level, b: Level): boolean {
  if (a === b) return true;
  if (a.kind !== b.kind || a.hash !== b.hash) return false;
  switch (a.kind) {
    case "zero":
      return true;
    case "param":
      return a.name === (b as Param).name;
    case "succ":
      return levelEqStructural(a.of, (b as Succ).of);
    case "max":
    case "imax":
      return levelEqStructural(a.lhs, (b as Max | IMax).lhs) && levelEqStructural(a.rhs, (b as Max | IMax).rhs);
  }
}

export function ofNat(n: number): Level {
  let l: Level = zero;
  for (let i = 0; i < n; i++) l = succ(l);
  return l;
}

/** Substitutes level parameters. Unmentioned parameters are left alone. */
export function instantiateLevel(l: Level, ps: readonly Name[], ls: readonly Level[]): Level {
  if (!hasParam(l)) return l;
  switch (l.kind) {
    case "zero":
      return l;
    case "param": {
      const i = ps.indexOf(l.name);
      return i >= 0 ? ls[i]! : l;
    }
    case "succ":
      return succ(instantiateLevel(l.of, ps, ls));
    case "max":
      return max(instantiateLevel(l.lhs, ps, ls), instantiateLevel(l.rhs, ps, ls));
    case "imax":
      return imax(instantiateLevel(l.lhs, ps, ls), instantiateLevel(l.rhs, ps, ls));
  }
}

/** The parameters occurring in `l`, added to `out`. */
export function collectParams(l: Level, out: Set<Name>): Set<Name> {
  switch (l.kind) {
    case "zero":
      break;
    case "param":
      out.add(l.name);
      break;
    case "succ":
      collectParams(l.of, out);
      break;
    case "max":
    case "imax":
      collectParams(l.lhs, out);
      collectParams(l.rhs, out);
      break;
  }
  return out;
}

// ---- Decision procedure ----------------------------------------------------------

/** A level without `imax`, as a set of terms: `param + k` (name) or `k` (null). */
interface Term {
  readonly param: Name | null;
  readonly offset: number;
}

/** Parameters that occur somewhere in the second argument of an `imax`. */
function imaxRhsParams(l: Level, out: Set<Name>): void {
  switch (l.kind) {
    case "zero":
    case "param":
      return;
    case "succ":
      imaxRhsParams(l.of, out);
      return;
    case "max":
      imaxRhsParams(l.lhs, out);
      imaxRhsParams(l.rhs, out);
      return;
    case "imax":
      imaxRhsParams(l.lhs, out);
      imaxRhsParams(l.rhs, out);
      collectParams(l.rhs, out);
      return;
  }
}

/**
 * Under an assignment saying which parameters are zero (`zeroes`), flattens
 * `l` into terms. Parameters not in `zeroes` are known to be >= 1 if listed
 * in `positive`, which is what makes `imax` decidable here.
 */
function terms(l: Level, zeroes: ReadonlySet<Name>, positive: ReadonlySet<Name>, offset: number, out: Term[]): void {
  switch (l.kind) {
    case "zero":
      out.push({ param: null, offset });
      return;
    case "param":
      out.push(zeroes.has(l.name) ? { param: null, offset } : { param: l.name, offset });
      return;
    case "succ":
      terms(l.of, zeroes, positive, offset + 1, out);
      return;
    case "max":
      terms(l.lhs, zeroes, positive, offset, out);
      terms(l.rhs, zeroes, positive, offset, out);
      return;
    case "imax":
      if (isZeroUnder(l.rhs, zeroes, positive)) {
        out.push({ param: null, offset });
      } else {
        terms(l.lhs, zeroes, positive, offset, out);
        terms(l.rhs, zeroes, positive, offset, out);
      }
      return;
  }
}

/** Whether `l` is 0 under the assignment. Every parameter of `l` must be decided. */
function isZeroUnder(l: Level, zeroes: ReadonlySet<Name>, positive: ReadonlySet<Name>): boolean {
  switch (l.kind) {
    case "zero":
      return true;
    case "param":
      if (zeroes.has(l.name)) return true;
      if (positive.has(l.name)) return false;
      throw new Error(`level parameter ${nameToString(l.name)} undecided`);
    case "succ":
      return false;
    case "max":
      return isZeroUnder(l.lhs, zeroes, positive) && isZeroUnder(l.rhs, zeroes, positive);
    case "imax":
      return isZeroUnder(l.rhs, zeroes, positive);
  }
}

/**
 * `l1 >= l2` holds for all values of the remaining (unconstrained) parameters,
 * given maxima of terms. Parameters in `positive` are >= 1.
 */
function termsGeq(t1: readonly Term[], t2: readonly Term[], positive: ReadonlySet<Name>): boolean {
  // Each term of t2 must be dominated by some term of t1 for every assignment.
  // Since all values are naturals and t1 is a max, it suffices that each t2 term
  // is dominated by a single t1 term (the max of naturals is attained).
  for (const b of t2) {
    let ok = false;
    for (const a of t1) {
      if (b.param === null) {
        // constant k: dominated by c >= k, or by p + j with j + (p >= 1 ? 1 : 0) >= k.
        const lo = a.param === null ? a.offset : a.offset + (positive.has(a.param) ? 1 : 0);
        if (lo >= b.offset) ok = true;
      } else if (a.param === b.param && a.offset >= b.offset) {
        ok = true;
      }
      if (ok) break;
    }
    if (!ok) return false;
  }
  return true;
}

/** Decides `l1 >= l2` for all assignments of the parameters. */
export function geq(l1: Level, l2: Level): boolean {
  if (levelEqStructural(l1, l2) || l2.kind === "zero") return true;
  const split = new Set<Name>();
  imaxRhsParams(l1, split);
  imaxRhsParams(l2, split);
  const params = [...split];
  const zeroes = new Set<Name>();
  const positive = new Set<Name>();
  const go = (i: number): boolean => {
    if (i === params.length) {
      const t1: Term[] = [];
      const t2: Term[] = [];
      terms(l1, zeroes, positive, 0, t1);
      terms(l2, zeroes, positive, 0, t2);
      return termsGeq(t1, t2, positive);
    }
    const p = params[i]!;
    zeroes.add(p);
    const a = go(i + 1);
    zeroes.delete(p);
    if (!a) return false;
    positive.add(p);
    const b = go(i + 1);
    positive.delete(p);
    return b;
  };
  return go(0);
}

/** Decides `l1 = l2` for all assignments of the parameters. */
export function levelEquiv(l1: Level, l2: Level): boolean {
  return levelEqStructural(l1, l2) || (geq(l1, l2) && geq(l2, l1));
}

/** Whether `l` is 0 for every assignment, or nonzero for every assignment. */
export function isNeverZero(l: Level): boolean {
  return geq(l, succ(zero));
}
export function isAlwaysZero(l: Level): boolean {
  return geq(zero, l);
}

export function levelToString(l: Level): string {
  switch (l.kind) {
    case "zero":
      return "0";
    case "param":
      return nameToString(l.name);
    case "succ": {
      let n = 1;
      let b: Level = l.of;
      while (b.kind === "succ") {
        n++;
        b = b.of;
      }
      return b.kind === "zero" ? `${n}` : `${levelToString(b)}+${n}`;
    }
    case "max":
      return `max (${levelToString(l.lhs)}) (${levelToString(l.rhs)})`;
    case "imax":
      return `imax (${levelToString(l.lhs)}) (${levelToString(l.rhs)})`;
  }
}
