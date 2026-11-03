// Kernel expressions: locally nameless terms of Lean 4's type theory.
//
// Bound variables are de Bruijn indices (`bvar`). While checking under binders,
// the type checker replaces them with free variables (`fvar`), which carry their
// own type (and value, for `let`). Every node caches its hash, the number of
// loose bound variables it may contain, and whether it contains free variables
// or level parameters, so traversals can skip closed subterms.

import { type Level, hasParam, instantiateLevel, levelEqStructural, levelToString } from "./level.ts";
import { type Name, nameToString } from "./name.ts";

export type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit";

export type Expr = BVar | FVar | Sort | Const | App | Lam | Pi | Let | NatLit | StrLit | Proj;

interface Base {
  readonly hash: number;
  /** One more than the largest loose bound variable index (0 if closed). */
  readonly lbr: number;
  readonly hasFVar: boolean;
  readonly hasLevelParam: boolean;
}
export interface BVar extends Base {
  readonly kind: "bvar";
  readonly idx: number;
}
export interface FVar extends Base {
  readonly kind: "fvar";
  readonly id: number;
  readonly name: Name;
  readonly type: Expr;
  readonly value: Expr | undefined;
}
export interface Sort extends Base {
  readonly kind: "sort";
  readonly level: Level;
}
export interface Const extends Base {
  readonly kind: "const";
  readonly name: Name;
  readonly levels: readonly Level[];
}
export interface App extends Base {
  readonly kind: "app";
  readonly fn: Expr;
  readonly arg: Expr;
}
export interface Lam extends Base {
  readonly kind: "lam";
  readonly binderName: Name;
  readonly binderType: Expr;
  readonly body: Expr;
  readonly binderInfo: BinderInfo;
}
export interface Pi extends Base {
  readonly kind: "pi";
  readonly binderName: Name;
  readonly binderType: Expr;
  readonly body: Expr;
  readonly binderInfo: BinderInfo;
}
export interface Let extends Base {
  readonly kind: "let";
  readonly binderName: Name;
  readonly binderType: Expr;
  readonly value: Expr;
  readonly body: Expr;
}
export interface NatLit extends Base {
  readonly kind: "natLit";
  readonly value: bigint;
}
export interface StrLit extends Base {
  readonly kind: "strLit";
  readonly value: string;
}
export interface Proj extends Base {
  readonly kind: "proj";
  readonly typeName: Name;
  readonly idx: number;
  readonly struct: Expr;
}

// ---- Construction -------------------------------------------------------------

const mix = (a: number, b: number): number => (Math.imul(a ^ (b + 0x9e3779b9), 0x85ebca6b) ^ (a >>> 13)) | 0;

function hashString(s: string): number {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 0x01000193);
  return h | 0;
}

const bvarCache: BVar[] = [];
export function bvar(idx: number): BVar {
  let b = bvarCache[idx];
  if (b === undefined) {
    b = { kind: "bvar", idx, hash: mix(3, idx), lbr: idx + 1, hasFVar: false, hasLevelParam: false };
    if (idx < 1024) bvarCache[idx] = b;
  }
  return b;
}

let nextFVarId = 1;
export function fvar(name: Name, type: Expr, value?: Expr): FVar {
  const id = nextFVarId++;
  return { kind: "fvar", id, name, type, value, hash: mix(5, id), lbr: 0, hasFVar: true, hasLevelParam: false };
}

export function sort(level: Level): Sort {
  return { kind: "sort", level, hash: mix(7, level.hash), lbr: 0, hasFVar: false, hasLevelParam: hasParam(level) };
}

export function constant(name: Name, levels: readonly Level[]): Const {
  let h = mix(11, name.id);
  let hp = false;
  for (const l of levels) {
    h = mix(h, l.hash);
    hp ||= hasParam(l);
  }
  return { kind: "const", name, levels, hash: h, lbr: 0, hasFVar: false, hasLevelParam: hp };
}

export function app(fn: Expr, arg: Expr): App {
  return {
    kind: "app",
    fn,
    arg,
    hash: mix(mix(13, fn.hash), arg.hash),
    lbr: Math.max(fn.lbr, arg.lbr),
    hasFVar: fn.hasFVar || arg.hasFVar,
    hasLevelParam: fn.hasLevelParam || arg.hasLevelParam,
  };
}

export function apps(fn: Expr, args: readonly Expr[]): Expr {
  let e = fn;
  for (const a of args) e = app(e, a);
  return e;
}

export function lam(binderName: Name, binderType: Expr, body: Expr, binderInfo: BinderInfo = "default"): Lam {
  return {
    kind: "lam",
    binderName,
    binderType,
    body,
    binderInfo,
    hash: mix(mix(17, binderType.hash), body.hash),
    lbr: Math.max(binderType.lbr, body.lbr - 1),
    hasFVar: binderType.hasFVar || body.hasFVar,
    hasLevelParam: binderType.hasLevelParam || body.hasLevelParam,
  };
}

export function pi(binderName: Name, binderType: Expr, body: Expr, binderInfo: BinderInfo = "default"): Pi {
  return {
    kind: "pi",
    binderName,
    binderType,
    body,
    binderInfo,
    hash: mix(mix(19, binderType.hash), body.hash),
    lbr: Math.max(binderType.lbr, body.lbr - 1),
    hasFVar: binderType.hasFVar || body.hasFVar,
    hasLevelParam: binderType.hasLevelParam || body.hasLevelParam,
  };
}

export function letE(binderName: Name, binderType: Expr, value: Expr, body: Expr): Let {
  return {
    kind: "let",
    binderName,
    binderType,
    value,
    body,
    hash: mix(mix(mix(23, binderType.hash), value.hash), body.hash),
    lbr: Math.max(binderType.lbr, value.lbr, body.lbr - 1),
    hasFVar: binderType.hasFVar || value.hasFVar || body.hasFVar,
    hasLevelParam: binderType.hasLevelParam || value.hasLevelParam || body.hasLevelParam,
  };
}

export function natLit(value: bigint): NatLit {
  if (value < 0n) throw new Error("negative natural number literal");
  return { kind: "natLit", value, hash: mix(29, hashString(value.toString())), lbr: 0, hasFVar: false, hasLevelParam: false };
}

export function strLit(value: string): StrLit {
  return { kind: "strLit", value, hash: mix(31, hashString(value)), lbr: 0, hasFVar: false, hasLevelParam: false };
}

export function proj(typeName: Name, idx: number, struct: Expr): Proj {
  return {
    kind: "proj",
    typeName,
    idx,
    struct,
    hash: mix(mix(37, typeName.id), mix(idx, struct.hash)),
    lbr: struct.lbr,
    hasFVar: struct.hasFVar,
    hasLevelParam: struct.hasLevelParam,
  };
}

// ---- Structure ---------------------------------------------------------------------

export function getAppFn(e: Expr): Expr {
  while (e.kind === "app") e = e.fn;
  return e;
}

export function getAppArgs(e: Expr): Expr[] {
  const args: Expr[] = [];
  while (e.kind === "app") {
    args.push(e.arg);
    e = e.fn;
  }
  return args.reverse();
}

export function getAppNumArgs(e: Expr): number {
  let n = 0;
  while (e.kind === "app") {
    n++;
    e = e.fn;
  }
  return n;
}

/** Alpha-equivalence (binder names and binder info are ignored). */
export function exprEq(a: Expr, b: Expr): boolean {
  if (a === b) return true;
  if (a.hash !== b.hash || a.kind !== b.kind) return false;
  switch (a.kind) {
    case "bvar":
      return a.idx === (b as BVar).idx;
    case "fvar":
      return a.id === (b as FVar).id;
    case "sort":
      return levelEqStructural(a.level, (b as Sort).level);
    case "const": {
      const c = b as Const;
      if (a.name !== c.name || a.levels.length !== c.levels.length) return false;
      for (let i = 0; i < a.levels.length; i++) if (!levelEqStructural(a.levels[i]!, c.levels[i]!)) return false;
      return true;
    }
    case "app": {
      // Iterate along the spine to avoid deep recursion on long applications.
      let x: Expr = a;
      let y: Expr = b;
      while (x.kind === "app" && y.kind === "app") {
        if (x === y) return true;
        if (x.hash !== y.hash || !exprEq(x.arg, y.arg)) return false;
        x = x.fn;
        y = y.fn;
      }
      return exprEq(x, y);
    }
    case "lam":
    case "pi": {
      const c = b as Lam | Pi;
      return exprEq(a.binderType, c.binderType) && exprEq(a.body, c.body);
    }
    case "let": {
      const c = b as Let;
      return exprEq(a.binderType, c.binderType) && exprEq(a.value, c.value) && exprEq(a.body, c.body);
    }
    case "natLit":
      return a.value === (b as NatLit).value;
    case "strLit":
      return a.value === (b as StrLit).value;
    case "proj": {
      const c = b as Proj;
      return a.typeName === c.typeName && a.idx === c.idx && exprEq(a.struct, c.struct);
    }
  }
}

// ---- Generic traversal -------------------------------------------------------------

/**
 * Rebuilds `e` bottom-up. `f(sub, depth)` may return a replacement for a
 * subterm (or `undefined` to recurse into it); `depth` is the number of
 * binders above the subterm. Unchanged subterms keep their identity.
 */
export function replace(e: Expr, f: (sub: Expr, depth: number) => Expr | undefined, depth = 0): Expr {
  const cache: Map<Expr, Expr>[] = [];
  const go = (e: Expr, d: number): Expr => {
    const r = f(e, d);
    if (r !== undefined) return r;
    let c = cache[d];
    if (c === undefined) {
      c = new Map();
      cache[d] = c;
    }
    const hit = c.get(e);
    if (hit !== undefined) return hit;
    let out: Expr;
    switch (e.kind) {
      case "app": {
        const fn = go(e.fn, d);
        const arg = go(e.arg, d);
        out = fn === e.fn && arg === e.arg ? e : app(fn, arg);
        break;
      }
      case "lam": {
        const t = go(e.binderType, d);
        const b = go(e.body, d + 1);
        out = t === e.binderType && b === e.body ? e : lam(e.binderName, t, b, e.binderInfo);
        break;
      }
      case "pi": {
        const t = go(e.binderType, d);
        const b = go(e.body, d + 1);
        out = t === e.binderType && b === e.body ? e : pi(e.binderName, t, b, e.binderInfo);
        break;
      }
      case "let": {
        const t = go(e.binderType, d);
        const v = go(e.value, d);
        const b = go(e.body, d + 1);
        out = t === e.binderType && v === e.value && b === e.body ? e : letE(e.binderName, t, v, b);
        break;
      }
      case "proj": {
        const s = go(e.struct, d);
        out = s === e.struct ? e : proj(e.typeName, e.idx, s);
        break;
      }
      default:
        out = e;
    }
    c.set(e, out);
    return out;
  };
  return go(e, depth);
}

// ---- Bound variables ---------------------------------------------------------------

/** Adds `amount` to every loose bound variable with index >= `start`. */
export function liftLooseBVars(e: Expr, amount: number, start = 0): Expr {
  if (amount === 0 || e.lbr <= start) return e;
  return replace(e, (s, d) => {
    if (s.lbr <= start + d) return s;
    if (s.kind === "bvar") return bvar(s.idx + amount);
    return undefined;
  });
}

/** Subtracts `amount` from every loose bound variable with index >= `start`. */
export function lowerLooseBVars(e: Expr, amount: number, start = amount): Expr {
  if (amount === 0 || e.lbr <= start) return e;
  return replace(e, (s, d) => {
    if (s.lbr <= start + d) return s;
    if (s.kind === "bvar") return bvar(s.idx - amount);
    return undefined;
  });
}

/**
 * Substitutes loose bound variables: `bvar i` (at binder depth d) becomes
 * `subst[i - d]` lifted by d, for i - d < subst.length; larger indices are
 * lowered by subst.length.
 */
export function instantiate(e: Expr, subst: readonly Expr[]): Expr {
  const n = subst.length;
  if (n === 0 || e.lbr === 0) return e;
  // Specialized traversal (this is the kernel's hottest function): closed
  // subterms are returned as is, and shared open subterms are cached per depth.
  const caches: (Map<Expr, Expr> | undefined)[] = [];
  const go = (x: Expr, d: number): Expr => {
    if (x.lbr <= d) return x;
    if (x.kind === "bvar") {
      const i = x.idx - d;
      return i < n ? liftLooseBVars(subst[i]!, d) : bvar(x.idx - n);
    }
    let c = caches[d];
    if (c === undefined) {
      c = new Map();
      caches[d] = c;
    } else {
      const hit = c.get(x);
      if (hit !== undefined) return hit;
    }
    let r: Expr;
    switch (x.kind) {
      case "app":
        r = app(go(x.fn, d), go(x.arg, d));
        break;
      case "lam":
        r = lam(x.binderName, go(x.binderType, d), go(x.body, d + 1), x.binderInfo);
        break;
      case "pi":
        r = pi(x.binderName, go(x.binderType, d), go(x.body, d + 1), x.binderInfo);
        break;
      case "let":
        r = letE(x.binderName, go(x.binderType, d), go(x.value, d), go(x.body, d + 1));
        break;
      case "proj":
        r = proj(x.typeName, x.idx, go(x.struct, d));
        break;
      default:
        r = x;
    }
    c.set(x, r);
    return r;
  };
  return go(e, 0);
}

/** `instantiate(body, [v])`: the body of a binder applied to `v`. */
export function instantiate1(body: Expr, v: Expr): Expr {
  return instantiate(body, [v]);
}

/** Like `instantiate`, but `subst` is in binder order: the last element replaces `bvar 0`. */
export function instantiateRev(e: Expr, subst: readonly Expr[]): Expr {
  return instantiate(e, [...subst].reverse());
}

/**
 * Replaces each free variable `xs[i]` with `bvar (n - 1 - i)` (adjusted for
 * depth), so that `instantiateRev(abstract(e, xs), xs) == e`.
 */
export function abstract(e: Expr, xs: readonly FVar[]): Expr {
  if (!e.hasFVar || xs.length === 0) return e;
  const n = xs.length;
  const pos = new Map<number, number>();
  xs.forEach((x, i) => pos.set(x.id, i));
  return replace(e, (s, d) => {
    if (!s.hasFVar) return s;
    if (s.kind === "fvar") {
      const i = pos.get(s.id);
      return i === undefined ? s : bvar(d + n - 1 - i);
    }
    return undefined;
  });
}

export function hasLooseBVar(e: Expr, idx: number): boolean {
  let found = false;
  replace(e, (s, d) => {
    if (found || s.lbr <= idx + d) return s;
    if (s.kind === "bvar") {
      if (s.idx === idx + d) found = true;
      return s;
    }
    return undefined;
  });
  return found;
}

/** Whether `e` contains the free variable `x`. */
export function hasFVarId(e: Expr, x: FVar): boolean {
  let found = false;
  replace(e, (s) => {
    if (found || !s.hasFVar) return s;
    if (s.kind === "fvar") {
      if (s.id === x.id) found = true;
      return s;
    }
    return undefined;
  });
  return found;
}

// ---- Level parameters --------------------------------------------------------------

export function instantiateLevelParams(e: Expr, ps: readonly Name[], ls: readonly Level[]): Expr {
  if (!e.hasLevelParam || ps.length === 0) return e;
  return replace(e, (s) => {
    if (!s.hasLevelParam) return s;
    if (s.kind === "sort") return sort(instantiateLevel(s.level, ps, ls));
    if (s.kind === "const") return constant(s.name, s.levels.map((l) => instantiateLevel(l, ps, ls)));
    return undefined;
  });
}

// ---- Binder telescopes -------------------------------------------------------------

/** `Π (x₁ : A₁) … (xₙ : Aₙ), b` over free variables `xs`. */
export function mkPi(xs: readonly FVar[], b: Expr): Expr {
  let r = abstract(b, xs);
  for (let i = xs.length - 1; i >= 0; i--) {
    const x = xs[i]!;
    r = pi(x.name, abstract(x.type, xs.slice(0, i)), r);
  }
  return r;
}

/** `λ (x₁ : A₁) … (xₙ : Aₙ), b` over free variables `xs`. */
export function mkLambda(xs: readonly FVar[], b: Expr): Expr {
  let r = abstract(b, xs);
  for (let i = xs.length - 1; i >= 0; i--) {
    const x = xs[i]!;
    r = lam(x.name, abstract(x.type, xs.slice(0, i)), r);
  }
  return r;
}

// ---- Printing ----------------------------------------------------------------------

export function exprToString(e: Expr, depth = 0): string {
  if (depth > 40) return "…";
  switch (e.kind) {
    case "bvar":
      return `#${e.idx}`;
    case "fvar":
      return `${nameToString(e.name)}@${e.id}`;
    case "sort":
      return `Sort (${levelToString(e.level)})`;
    case "const":
      return e.levels.length === 0
        ? nameToString(e.name)
        : `${nameToString(e.name)}.{${e.levels.map(levelToString).join(", ")}}`;
    case "app":
      return `(${exprToString(getAppFn(e), depth + 1)} ${getAppArgs(e).map((a) => exprToString(a, depth + 1)).join(" ")})`;
    case "lam":
      return `(fun (${nameToString(e.binderName)} : ${exprToString(e.binderType, depth + 1)}) => ${exprToString(e.body, depth + 1)})`;
    case "pi":
      return `((${nameToString(e.binderName)} : ${exprToString(e.binderType, depth + 1)}) -> ${exprToString(e.body, depth + 1)})`;
    case "let":
      return `(let ${nameToString(e.binderName)} : ${exprToString(e.binderType, depth + 1)} := ${exprToString(e.value, depth + 1)}; ${exprToString(e.body, depth + 1)})`;
    case "natLit":
      return `${e.value}`;
    case "strLit":
      return JSON.stringify(e.value);
    case "proj":
      return `${exprToString(e.struct, depth + 1)}.${nameToString(e.typeName)}#${e.idx}`;
  }
}

/** Visits subterms; `f` returns whether to descend into the subterm. */
export function visit(e: Expr, f: (sub: Expr, depth: number) => boolean, depth = 0): void {
  if (!f(e, depth)) return;
  switch (e.kind) {
    case "app":
      visit(e.fn, f, depth);
      visit(e.arg, f, depth);
      return;
    case "lam":
    case "pi":
      visit(e.binderType, f, depth);
      visit(e.body, f, depth + 1);
      return;
    case "let":
      visit(e.binderType, f, depth);
      visit(e.value, f, depth);
      visit(e.body, f, depth + 1);
      return;
    case "proj":
      visit(e.struct, f, depth);
      return;
    default:
      return;
  }
}

/** Whether some subterm satisfies `p`. */
export function exprAny(e: Expr, p: (sub: Expr) => boolean): boolean {
  let found = false;
  const seen = new Set<Expr>();
  visit(e, (s) => {
    if (found || seen.has(s)) return false;
    seen.add(s);
    if (p(s)) {
      found = true;
      return false;
    }
    return true;
  });
  return found;
}

const OptParam = "optParam";
const AutoParam = "autoParam";
const OutParam = "outParam";
const SemiOutParam = "semiOutParam";

/** Strips `optParam`/`autoParam`/`outParam`/`semiOutParam` wrappers (Lean's `consumeTypeAnnotations`). */
export function consumeTypeAnnotations(e: Expr): Expr {
  for (;;) {
    const f = getAppFn(e);
    if (f.kind !== "const" || f.name.kind !== "str" || f.name.prefix.kind !== "anonymous") return e;
    const n = getAppNumArgs(e);
    const s = f.name.str;
    if ((s === OptParam || s === AutoParam) && n === 2) e = ((e as App).fn as App).arg;
    else if ((s === OutParam || s === SemiOutParam) && n === 1) e = (e as App).arg;
    else return e;
  }
}
