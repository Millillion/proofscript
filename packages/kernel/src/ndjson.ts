// Reader for the lean4export NDJSON format (version 3.x):
// https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
//
// The reader only builds data; it checks nothing about the logic. Malformed
// input (dangling indices, duplicate indices, unknown objects) is an error.

import {
  type AxiomInfo,
  type ConstructorInfo,
  type Declaration,
  type DefinitionInfo,
  type DefinitionSafety,
  type InductiveInfo,
  KernelError,
  type OpaqueInfo,
  type QuotInfo,
  type QuotKind,
  type RecursorInfo,
  type ReducibilityHints,
  type TheoremInfo,
} from "./env.ts";
import { type BinderInfo, type Expr, app, bvar, constant, lam, letE, natLit, pi, proj, sort, strLit } from "./expr.ts";
import { type Level, imax, max, param, succ, zero } from "./level.ts";
import { type Name, anonymous, numName, strName } from "./name.ts";

export interface ExportFile {
  readonly meta: unknown;
  readonly declarations: Declaration[];
}

type Json = { [k: string]: any };

/** Reads an export incrementally; `line` returns the declarations completed by that line. */
export class ExportReader {
  meta: unknown = undefined;
  readonly #feed: (line: string, lineNo: number) => Declaration[];
  #lineNo = 0;
  /** A quotient block may span several lines; it is held here until complete. */
  #pendingQuot: QuotInfo[] = [];

  constructor() {
    this.#feed = makeFeeder(this);
  }

  line(line: string): Declaration[] {
    this.#lineNo++;
    if (line.trim() === "") return [];
    return this.#feed(line, this.#lineNo);
  }

  /** Flushes anything held back (an incomplete quotient block). */
  end(): Declaration[] {
    if (this.#pendingQuot.length === 0) return [];
    const q: Declaration = { kind: "quot", infos: this.#pendingQuot };
    this.#pendingQuot = [];
    return [q];
  }

  get pendingQuot(): QuotInfo[] {
    return this.#pendingQuot;
  }
  set pendingQuot(q: QuotInfo[]) {
    this.#pendingQuot = q;
  }
}

export function parseExport(text: string): ExportFile {
  const r = new ExportReader();
  const declarations: Declaration[] = [];
  for (const line of text.split("\n")) declarations.push(...r.line(line));
  declarations.push(...r.end());
  return { meta: r.meta, declarations };
}

function makeFeeder(reader: ExportReader): (line: string, lineNo: number) => Declaration[] {
  const names: Name[] = [anonymous];
  const levels: Level[] = [zero];
  const exprs: Expr[] = [];

  const getName = (i: unknown): Name => {
    if (typeof i !== "number" || names[i] === undefined) throw new KernelError(`bad name index ${String(i)}`);
    return names[i]!;
  };
  const getLevel = (i: unknown): Level => {
    if (typeof i !== "number" || levels[i] === undefined) throw new KernelError(`bad level index ${String(i)}`);
    return levels[i]!;
  };
  const getExpr = (i: unknown): Expr => {
    if (typeof i !== "number" || exprs[i] === undefined) throw new KernelError(`bad expression index ${String(i)}`);
    return exprs[i]!;
  };
  const getNat = (i: unknown): number => {
    if (typeof i !== "number" || !Number.isSafeInteger(i) || i < 0) throw new KernelError(`bad natural number ${String(i)}`);
    return i;
  };
  const getBool = (b: unknown): boolean => {
    if (typeof b !== "boolean") throw new KernelError(`bad boolean ${String(b)}`);
    return b;
  };
  const getNames = (a: unknown): Name[] => {
    if (!Array.isArray(a)) throw new KernelError("expected an array of names");
    return a.map(getName);
  };
  const binderInfo = (b: unknown): BinderInfo => {
    if (b === "default" || b === "implicit" || b === "strictImplicit" || b === "instImplicit") return b;
    throw new KernelError(`bad binder info ${String(b)}`);
  };
  const setAt = <T>(arr: T[], i: unknown, v: T, what: string): void => {
    if (typeof i !== "number" || !Number.isSafeInteger(i) || i < 0) throw new KernelError(`bad ${what} index ${String(i)}`);
    if (arr[i] !== undefined) throw new KernelError(`duplicate ${what} index ${i}`);
    arr[i] = v;
  };

  const base = (o: Json) => ({
    name: getName(o.name),
    levelParams: getNames(o.levelParams),
    type: getExpr(o.type),
  });

  const inductiveVal = (o: Json): InductiveInfo => ({
    kind: "inductive",
    ...base(o),
    numParams: getNat(o.numParams),
    numIndices: getNat(o.numIndices),
    all: getNames(o.all),
    ctors: getNames(o.ctors),
    numNested: getNat(o.numNested),
    isRec: getBool(o.isRec),
    isUnsafe: getBool(o.isUnsafe),
    isReflexive: getBool(o.isReflexive),
  });
  const ctorVal = (o: Json): ConstructorInfo => ({
    kind: "constructor",
    ...base(o),
    induct: getName(o.induct),
    cidx: getNat(o.cidx),
    numParams: getNat(o.numParams),
    numFields: getNat(o.numFields),
    isUnsafe: getBool(o.isUnsafe),
  });
  const recVal = (o: Json): RecursorInfo => {
    if (!Array.isArray(o.rules)) throw new KernelError("recursor rules must be an array");
    return {
      kind: "recursor",
      ...base(o),
      all: getNames(o.all),
      numParams: getNat(o.numParams),
      numIndices: getNat(o.numIndices),
      numMotives: getNat(o.numMotives),
      numMinors: getNat(o.numMinors),
      rules: o.rules.map((r: Json) => ({ ctor: getName(r.ctor), nfields: getNat(r.nfields), rhs: getExpr(r.rhs) })),
      k: getBool(o.k),
      isUnsafe: getBool(o.isUnsafe),
    };
  };
  const hints = (h: unknown): ReducibilityHints => {
    if (h === "opaque") return { kind: "opaque" };
    if (h === "abbrev") return { kind: "abbrev" };
    if (typeof h === "object" && h !== null && "regular" in h) return { kind: "regular", height: getNat((h as Json).regular) };
    throw new KernelError(`bad reducibility hints ${JSON.stringify(h)}`);
  };
  const safety = (s: unknown): DefinitionSafety => {
    if (s === "safe" || s === "unsafe" || s === "partial") return s;
    throw new KernelError(`bad definition safety ${String(s)}`);
  };

  return (line: string, lineNo: number): Declaration[] => {
    const declarations: Declaration[] = [];
    let o: Json;
    try {
      o = JSON.parse(line) as Json;
    } catch {
      throw new KernelError(`line ${lineNo}: invalid JSON`);
    }
    // A quotient block ends after its four constants, or at the next declaration.
    const isDecl = "axiom" in o || "def" in o || "thm" in o || "opaque" in o || "inductive" in o;
    if (isDecl && reader.pendingQuot.length > 0) {
      declarations.push({ kind: "quot", infos: reader.pendingQuot });
      reader.pendingQuot = [];
    }
    if ("meta" in o) reader.meta = o.meta;
    else if ("str" in o) setAt(names, o.in, strName(getName(o.str.pre), String(o.str.str)), "name");
    else if ("num" in o) setAt(names, o.in, numName(getName(o.num.pre), BigInt(getNat(o.num.i))), "name");
    else if ("succ" in o) setAt(levels, o.il, succ(getLevel(o.succ)), "level");
    else if ("max" in o) setAt(levels, o.il, max(getLevel(o.max[0]), getLevel(o.max[1])), "level");
    else if ("imax" in o) setAt(levels, o.il, imax(getLevel(o.imax[0]), getLevel(o.imax[1])), "level");
    else if ("param" in o) setAt(levels, o.il, param(getName(o.param)), "level");
    else if ("bvar" in o) setAt(exprs, o.ie, bvar(getNat(o.bvar)), "expression");
    else if ("sort" in o) setAt(exprs, o.ie, sort(getLevel(o.sort)), "expression");
    else if ("const" in o) {
      if (!Array.isArray(o.const.us)) throw new KernelError(`line ${lineNo}: bad universe list`);
      setAt(exprs, o.ie, constant(getName(o.const.name), o.const.us.map(getLevel)), "expression");
    } else if ("app" in o) setAt(exprs, o.ie, app(getExpr(o.app.fn), getExpr(o.app.arg)), "expression");
    else if ("lam" in o)
      setAt(exprs, o.ie, lam(getName(o.lam.name), getExpr(o.lam.type), getExpr(o.lam.body), binderInfo(o.lam.binderInfo)), "expression");
    else if ("forallE" in o)
      setAt(exprs, o.ie, pi(getName(o.forallE.name), getExpr(o.forallE.type), getExpr(o.forallE.body), binderInfo(o.forallE.binderInfo)), "expression");
    else if ("letE" in o)
      setAt(exprs, o.ie, letE(getName(o.letE.name), getExpr(o.letE.type), getExpr(o.letE.value), getExpr(o.letE.body)), "expression");
    else if ("proj" in o) setAt(exprs, o.ie, proj(getName(o.proj.typeName), getNat(o.proj.idx), getExpr(o.proj.struct)), "expression");
    else if ("natVal" in o) {
      if (typeof o.natVal !== "string" || !/^[0-9]+$/.test(o.natVal)) throw new KernelError(`line ${lineNo}: bad natVal`);
      setAt(exprs, o.ie, natLit(BigInt(o.natVal)), "expression");
    } else if ("strVal" in o) {
      if (typeof o.strVal !== "string") throw new KernelError(`line ${lineNo}: bad strVal`);
      setAt(exprs, o.ie, strLit(o.strVal), "expression");
    } else if ("mdata" in o) setAt(exprs, o.ie, getExpr(o.mdata.expr), "expression");
    else if ("axiom" in o) {
      const info: AxiomInfo = { kind: "axiom", ...base(o.axiom), isUnsafe: getBool(o.axiom.isUnsafe) };
      declarations.push({ kind: "axiom", info });
    } else if ("def" in o) {
      const d = o.def;
      const info: DefinitionInfo = {
        kind: "definition",
        ...base(d),
        value: getExpr(d.value),
        hints: hints(d.hints),
        safety: safety(d.safety),
        all: getNames(d.all),
      };
      declarations.push({ kind: "definition", info });
    } else if ("thm" in o) {
      const info: TheoremInfo = { kind: "theorem", ...base(o.thm), value: getExpr(o.thm.value), all: getNames(o.thm.all) };
      declarations.push({ kind: "theorem", info });
    } else if ("opaque" in o) {
      const d = o.opaque;
      const info: OpaqueInfo = { kind: "opaque", ...base(d), value: getExpr(d.value), isUnsafe: getBool(d.isUnsafe), all: getNames(d.all) };
      declarations.push({ kind: "opaque", info });
    } else if ("quot" in o) {
      const k = o.quot.kind;
      if (k !== "type" && k !== "ctor" && k !== "lift" && k !== "ind") throw new KernelError(`line ${lineNo}: bad quot kind`);
      const info: QuotInfo = { kind: "quot", ...base(o.quot), quotKind: k as QuotKind };
      // The four quotient constants arrive as consecutive objects; group them.
      reader.pendingQuot = [...reader.pendingQuot, info];
      if (reader.pendingQuot.length === 4) {
        declarations.push({ kind: "quot", infos: reader.pendingQuot });
        reader.pendingQuot = [];
      }
    } else if ("inductive" in o) {
      const d = o.inductive;
      if (!Array.isArray(d.types) || !Array.isArray(d.ctors) || !Array.isArray(d.recs)) {
        throw new KernelError(`line ${lineNo}: bad inductive declaration`);
      }
      declarations.push({ kind: "inductive", types: d.types.map(inductiveVal), ctors: d.ctors.map(ctorVal), recs: d.recs.map(recVal) });
    } else {
      throw new KernelError(`line ${lineNo}: unknown export object`);
    }
    return declarations;
  };
}
