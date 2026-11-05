// Authentication of Lean library constants in certificates.
//
// A certificate carries the Lean library declarations its proofs use. Proofs need no
// authentication (the kernel checks them, and any proof of the statement will do), but the
// *meaning* of a statement depends on the definitions and types it mentions: a certificate
// that redefined `Nat.add` or `Nat.le` could prove anything about them. So every library
// constant that a bound statement depends on, through types and definition bodies, must be
// exactly the one from the pinned Lean toolchain. `library.json` holds a content hash for
// each such constant, computed from an export of the toolchain's own library
// (`scripts/library.ts`), and the binder kinds of the constants the elaborator applies.

import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { type ConstantInfo, type Environment, type Expr, type Level, type Name, nameToString } from "@proofscript/kernel";

export interface LibraryTable {
  readonly toolchain: string;
  readonly constants: Readonly<Record<string, { readonly hash: string; readonly binders?: string }>>;
}

let table: LibraryTable | undefined;
export function libraryTable(): LibraryTable {
  table ??= JSON.parse(readFileSync(new URL("./library.json", import.meta.url), "utf8")) as LibraryTable;
  return table;
}

function h(...parts: string[]): string {
  return createHash("sha256").update(parts.join("\u0000")).digest("hex").slice(0, 32);
}

function levelKey(l: Level): string {
  switch (l.kind) {
    case "zero":
      return "0";
    case "succ":
      return `s(${levelKey(l.of)})`;
    case "max":
      return `m(${levelKey(l.lhs)},${levelKey(l.rhs)})`;
    case "imax":
      return `i(${levelKey(l.lhs)},${levelKey(l.rhs)})`;
    case "param":
      return `p(${nameToString(l.name)})`;
  }
}

/** Content hashes of expressions (binder names and kinds excluded: they carry no meaning). */
export class Hasher {
  readonly #memo = new WeakMap<Expr, string>();

  expr(e: Expr): string {
    const hit = this.#memo.get(e);
    if (hit !== undefined) return hit;
    let r: string;
    switch (e.kind) {
      case "bvar":
        r = h("b", String(e.idx));
        break;
      case "fvar":
        throw new Error("free variable in a declaration");
      case "sort":
        r = h("S", levelKey(e.level));
        break;
      case "const":
        r = h("C", nameToString(e.name), ...e.levels.map(levelKey));
        break;
      case "app":
        r = h("A", this.expr(e.fn), this.expr(e.arg));
        break;
      case "lam":
        r = h("L", this.expr(e.binderType), this.expr(e.body));
        break;
      case "pi":
        r = h("P", this.expr(e.binderType), this.expr(e.body));
        break;
      case "let":
        r = h("E", this.expr(e.binderType), this.expr(e.value), this.expr(e.body));
        break;
      case "natLit":
        r = h("N", e.value.toString());
        break;
      case "strLit":
        r = h("T", e.value);
        break;
      case "proj":
        r = h("J", nameToString(e.typeName), String(e.idx), this.expr(e.struct));
        break;
    }
    this.#memo.set(e, r);
    return r;
  }

  constant(c: ConstantInfo): string {
    const head = [c.kind, nameToString(c.name), c.levelParams.map(nameToString).join(","), this.expr(c.type)];
    switch (c.kind) {
      case "definition":
        return h(...head, c.safety, this.expr(c.value));
      case "opaque":
        return h(...head, String(c.isUnsafe), this.expr(c.value));
      case "axiom":
        return h(...head, String(c.isUnsafe));
      case "theorem":
        return h(...head);
      case "inductive":
        return h(...head, String(c.numParams), String(c.numIndices), c.all.map(nameToString).join(","), c.ctors.map(nameToString).join(","), String(c.isUnsafe));
      case "constructor":
        return h(...head, nameToString(c.induct), String(c.cidx), String(c.numParams), String(c.numFields), String(c.isUnsafe));
      case "recursor":
        // Derived by the kernel from its inductive type (which is authenticated itself).
        return h(c.kind, nameToString(c.name), c.all.map(nameToString).join(","));
      case "quot":
        // Installed canonically by the kernel.
        return h(c.kind, nameToString(c.name));
    }
  }
}

/** The constants a constant's meaning depends on: its type, and its value if a definition. */
export function meaningDeps(c: ConstantInfo, out: (n: Name) => void): void {
  const walk = (e: Expr) => {
    const seen = new Set<Expr>();
    const stack = [e];
    while (stack.length > 0) {
      const x = stack.pop()!;
      if (seen.has(x)) continue;
      seen.add(x);
      switch (x.kind) {
        case "const":
          out(x.name);
          break;
        case "app":
          stack.push(x.fn, x.arg);
          break;
        case "lam":
        case "pi":
          stack.push(x.binderType, x.body);
          break;
        case "let":
          stack.push(x.binderType, x.value, x.body);
          break;
        case "proj":
          out(x.typeName);
          stack.push(x.struct);
          break;
        default:
          break;
      }
    }
  };
  // A theorem's proof carries no meaning; its type is proved, so it needs no authentication.
  if (c.kind === "theorem") return;
  walk(c.type);
  if (c.kind === "definition" || c.kind === "opaque") walk(c.value);
  if (c.kind === "inductive") for (const n of [...c.all, ...c.ctors]) out(n);
  if (c.kind === "constructor") out(c.induct);
  if (c.kind === "recursor") for (const n of c.all) out(n);
}

/**
 * Checks that every library constant reachable from `roots` (through meaning, see
 * `meaningDeps`) is the pinned toolchain's. `isOwn` names the project's own constants,
 * which are bound separately (and not followed here). Returns the first offending constant.
 */
export function authenticate(env: Environment, roots: Iterable<Name>, isOwn: (n: string) => boolean, hasher: Hasher, ok: Set<string>): string | undefined {
  const lib = libraryTable().constants;
  const stack = [...roots];
  while (stack.length > 0) {
    const n = stack.pop()!;
    const s = nameToString(n);
    if (ok.has(s) || isOwn(s)) continue;
    const c = env.get(n);
    if (c === undefined) return `${s} (missing)`;
    // A theorem only ever stands for a proof: the kernel has checked it, and which proof it
    // is cannot change a statement's meaning.
    if (c.kind === "theorem") {
      ok.add(s);
      continue;
    }
    const expected = lib[s];
    if (expected === undefined || expected.hash !== hasher.constant(c)) return s;
    ok.add(s);
    meaningDeps(c, (d) => stack.push(d));
  }
  return undefined;
}
