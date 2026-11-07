// Proof certificates: check a project's proofs without Lean.
//
// `proofscript check --write-certificate` proves with Lean as usual and saves the kernel
// export of every checked declaration (`proofscript.cert`, gzipped NDJSON with a header).
// `proofscript check --certificate` then needs only TypeScript and Node:
//
//   1. Every declaration in the certificate is re-checked by ProofScript's kernel.
//   2. The project is translated again, and each declaration is *bound*: ProofScript
//      elaborates the generated statement itself (elab.ts) and the kernel decides whether
//      the certificate's declaration has exactly that type. Definitions are bound by their
//      signatures and their equations (`f params = body`, proved in the certificate),
//      inductive types by their constructors. Library constants a statement depends on must
//      be the pinned toolchain's (library.ts).
//   3. A theorem is verified only if it and everything its statement depends on is bound.
//      Anything else (a changed statement, a new theorem, syntax the elaborator does not
//      handle) needs Lean, and is reported as such, never as verified.
//
// What a certificate cannot show: that a recursive function terminates. Its equation pins it
// down only if it does; the certificate's own definition was proved terminating by Lean when
// the certificate was made. This is reported as an assumption of each result.

import { readFileSync, writeFileSync } from "node:fs";
import { gunzipSync, gzipSync } from "node:zlib";
import {
  type Expr,
  getAppFn,
  Kernel,
  KernelError,
  type Name,
  TypeChecker,
  name as kname,
  nameToString,
  parseExport,
  visit,
} from "@proofscript/kernel";
import { type CheckResult, STANDARD_AXIOMS, type TheoremResult, footprint } from "./check.ts";
import { ElabError, Elaborator, HOLE, withHole } from "./elab.ts";
import { LEAN4EXPORT_COMMIT, LEAN_TOOLCHAIN } from "./lean.ts";
import { type Decl, ParseError, parseDecl } from "./lean-syntax.ts";
import { Hasher, authenticate, libraryTable } from "./library.ts";
import type { Project } from "./project.ts";
import { type Diagnostic, type GeneratedDecl, Translator } from "./translate.ts";

export const CERTIFICATE_FORMAT = "proofscript-certificate";
export const CERTIFICATE_VERSION = 1;

export interface CertificateHeader {
  readonly format: typeof CERTIFICATE_FORMAT;
  readonly version: number;
  readonly toolchain: string;
  readonly lean4export: string;
  /** The theorems the certificate was made for (informational: binding decides). */
  readonly theorems: readonly string[];
}

// ---- Definition equations ---------------------------------------------------------------------

/** Splits generated `def` source into its binder groups and its body. */
export function splitDef(src: string): { name: string; binders: string[]; type: string; body: string } | undefined {
  const m = /^(?:@\[[^\]]*\] )?def (\S+)/.exec(src);
  if (m === null) return undefined;
  let i = m[0].length;
  const binders: string[] = [];
  for (;;) {
    while (src[i] === " ") i++;
    const open = src[i];
    if (open !== "(" && open !== "{") break;
    let depth = 0;
    const start = i;
    for (; i < src.length; i++) {
      const c = src[i]!;
      if (c === "(" || c === "[" || c === "{") depth++;
      if (c === ")" || c === "]" || c === "}") depth--;
      if (depth === 0) break;
    }
    binders.push(src.slice(start, ++i));
  }
  const bodyAt = src.indexOf(":=\n", i);
  if (!src.startsWith(": ", i) || bodyAt < 0) return undefined;
  const type = src.slice(i + 2, bodyAt).trim();
  let body = src.slice(bodyAt + 3);
  const term = body.indexOf("\ntermination_by");
  if (term >= 0) body = body.slice(0, term);
  return { name: m[1]!, binders, type, body };
}

/** A binder group without its default (`(h : P := by tac)` → `(h : P)`), and its names. */
function plainBinder(b: string): { text: string; names: string[]; explicit: boolean } {
  let depth = 0;
  let cut = -1;
  for (let i = 0; i < b.length; i++) {
    const c = b[i]!;
    if (c === "(" || c === "[" || c === "{") depth++;
    if (c === ")" || c === "]" || c === "}") depth--;
    if (depth === 1 && b.startsWith(" := ", i)) {
      cut = i;
      break;
    }
  }
  const text = cut < 0 ? b : `${b.slice(0, cut)}${b[b.length - 1]}`;
  const colon = text.indexOf(" : ");
  return { text, names: text.slice(1, colon).trim().split(/\s+/), explicit: text[0] === "(" };
}

/** `theorem f.ps_eqn params : f args = (body)`, proved by unfolding `f` once. */
export function equationDecl(def: GeneratedDecl): GeneratedDecl | undefined {
  const parts = splitDef(def.source);
  if (parts === undefined) return undefined;
  const bs = parts.binders.map(plainBinder);
  const args = bs.filter((b) => b.explicit).flatMap((b) => b.names);
  const f = def.leanName;
  // Callee facts (`have _ : P := (g.post_0 x)`) are proofs; in a theorem's statement Lean
  // cannot elaborate them, and they carry no meaning, so the equation leaves them out.
  const body = withoutFacts(parts.body);
  const source =
    `theorem ${f}.ps_eqn${bs.map((b) => ` ${b.text}`).join("")} :\n    ${f}${args.map((a) => ` ${a}`).join("")} = (\n${body}) :=\n` +
    `  by first | (rw [${f}]; done) | (rw [${f}.eq_def]; done) | rfl`;
  return { kind: "theorem", aux: "eqn", tsName: `${def.tsName} (equation)`, leanName: `${f}.ps_eqn`, node: def.node, source, deps: new Set([f, ...def.deps]) };
}

/** Callee facts are proofs: equations (statements) leave them out. */
function withoutFacts(body: string): string {
  return body.replace(/^[ \t]*have _ : [^\n]*:= \(PS\.\S+\.post_\d+[^()\n]*\)\n/gm, "");
}

/** Occurrences of the name `f` itself (not `f.post_0`, not a longer name). */
const selfRef = (f: string) => new RegExp(`${f.replace(/[.]/g, "\\.")}(?![\\w.'])`, "g");

/** Size limits for generating uniqueness theorems (see `uniquenessDecl`). */
export const UNIQUENESS_MAX_CHARS = 10000;
export const UNIQUENESS_MAX_LETS = 8;

/**
 * For a recursive `f`: every function satisfying `f`'s equation is `f`.
 *
 * `theorem f.ps_unique (g : ∀ params, T) (hg : ∀ params, g args = body[g/f]) : ∀ params, g args = f args`
 *
 * An equation pins a recursive function down only if its recursion terminates; this theorem
 * is that fact, proved by Lean (by induction along `f`'s own recursion) when the certificate
 * is made, and bound like every other statement.
 */
export function uniquenessDecl(def: GeneratedDecl): GeneratedDecl | undefined {
  const parts = splitDef(def.source);
  if (parts === undefined) return undefined;
  const f = def.leanName;
  const body = withoutFacts(parts.body);
  if (!selfRef(f).test(body)) return undefined;
  // Lean's automatic proof grows with the body; on large loop bodies it has needed over
  // 17 GB. Those keep termination as an assumption (reported in results) instead.
  if (body.length > UNIQUENESS_MAX_CHARS || (body.match(/^\s*let /gm) ?? []).length > UNIQUENESS_MAX_LETS) return undefined;
  const plain = parts.binders.map(plainBinder);
  const args = plain.filter((b) => b.explicit).flatMap((b) => b.names);
  const g = "ps_g";
  const piType = `${parts.binders.map((b) => `${b} → `).join("")}${parts.type}`;
  const all = plain.map((b) => b.text).join(" ");
  const forall = (s: string) => (all === "" ? s : `∀ ${all}, ${s}`);
  const source =
    `theorem ${f}.ps_unique (${g} : ${piType})\n` +
    `    (hg : ${forall(`${g}${args.map((a) => ` ${a}`).join("")} = (\n${body.replace(selfRef(f), g)})`)}) :\n` +
    `    ${forall(`${g}${args.map((a) => ` ${a}`).join("")} = ${f}${args.map((a) => ` ${a}`).join("")}`)} := by\n` +
    `  ${plain.length === 0 ? "" : `intro ${plain.flatMap((b) => b.names).join(" ")}\n  `}` +
    `fun_induction ${f}${args.map((a) => ` ${a}`).join("")} <;> rw [hg] <;> clear hg <;> (try simp_all (config := { zetaDelta := true })) <;> (try (intros; omega))`;
  return { kind: "theorem", aux: "eqn", tsName: `${def.tsName} (uniqueness)`, leanName: `${f}.ps_unique`, node: def.node, source, deps: new Set([f, ...def.deps]) };
}

/** The declarations, each definition followed by its equation (and uniqueness, if recursive). */
export function withEquations(decls: readonly GeneratedDecl[]): GeneratedDecl[] {
  return decls.flatMap((d) => {
    if (d.kind !== "def") return [d];
    const out = [d];
    const e = equationDecl(d);
    if (e !== undefined) out.push(e);
    const u = uniquenessDecl(d);
    if (u !== undefined) out.push(u);
    return out;
  });
}

// ---- Files ------------------------------------------------------------------------------------

export function writeCertificate(path: string, exportText: string, theorems: readonly string[]): void {
  const header: CertificateHeader = { format: CERTIFICATE_FORMAT, version: CERTIFICATE_VERSION, toolchain: LEAN_TOOLCHAIN, lean4export: LEAN4EXPORT_COMMIT, theorems };
  writeFileSync(path, gzipSync(`${JSON.stringify(header)}\n${exportText}`, { level: 9 }));
}

export function readCertificate(path: string): { header: CertificateHeader; exportText: string } {
  const text = gunzipSync(readFileSync(path)).toString("utf8");
  const nl = text.indexOf("\n");
  const header = JSON.parse(nl < 0 ? text : text.slice(0, nl)) as CertificateHeader;
  if (header.format !== CERTIFICATE_FORMAT) throw new Error(`${path} is not a ProofScript certificate`);
  if (header.version !== CERTIFICATE_VERSION) throw new Error(`${path} has certificate format version ${header.version}; this ProofScript reads version ${CERTIFICATE_VERSION}`);
  return { header, exportText: nl < 0 ? "" : text.slice(nl + 1) };
}

// ---- Binding ----------------------------------------------------------------------------------

const kinds = (bs: readonly { implicit: boolean }[]) => bs.map((b) => (b.implicit ? "i" : "d")).join("");

function constantsOf(es: readonly Expr[], out: Set<Name>): void {
  for (const e of es) {
    visit(e, (s) => {
      // A hole stands for a proof (or an autoParam's tactic): what it is typed by is checked
      // where it is used, and carries no meaning of its own.
      if (s.kind === "app" && getAppFn(s).kind === "const" && (getAppFn(s) as { name: Name }).name === HOLE) return false;
      if (s.kind === "const") out.add(s.name);
      if (s.kind === "proj") out.add(s.typeName);
      return true;
    });
  }
}

class Binder {
  readonly #env;
  readonly #tc;
  readonly #own = new Map<string, { gen: GeneratedDecl; decl?: Decl; error?: string }>();
  readonly #infos = new Map<string, string>();
  readonly #state = new Map<string, true | string>();
  readonly #libOk = new Set<string>();
  readonly #hasher = new Hasher();
  /** Definitions whose equations mention themselves. */
  readonly recursive = new Set<string>();

  constructor(kernel: Kernel, decls: readonly GeneratedDecl[]) {
    this.#env = withHole(kernel.env);
    this.#tc = new TypeChecker(this.#env);
    for (const gen of decls) {
      try {
        const decl = parseDecl(gen.source);
        this.#own.set(gen.leanName, { gen, decl });
        this.#infos.set(gen.leanName, kinds(decl.binders));
        if (decl.k === "inductive") for (const c of decl.ctors) this.#infos.set(`${decl.name}.${c.name}`, decl.binders.map(() => "i").join("") + kinds(c.binders));
      } catch (e) {
        if (!(e instanceof ParseError)) throw e;
        this.#own.set(gen.leanName, { gen, error: `its generated source is outside what ProofScript elaborates (${e.message})` });
      }
    }
  }

  #elaborator(): Elaborator {
    const lib = libraryTable().constants;
    return new Elaborator(this.#env, (n) => this.#infos.get(n) ?? lib[n]?.binders);
  }

  /** Whether the certificate's declaration `n` is exactly the project's. `true`, or why not. */
  bind(n: string): true | string {
    const s = this.#state.get(n);
    if (s !== undefined) return s;
    this.#state.set(n, true); // recursion: a cycle is bound if everything else in it is
    let r: true | string;
    try {
      r = this.#bind(n);
    } catch (e) {
      if (!(e instanceof ElabError || e instanceof KernelError)) throw e;
      r = `${n}: ${e.message}`;
    }
    this.#state.set(n, r);
    return r;
  }

  #sameType(n: string, mine: Expr, kind: string): true | string {
    const c = this.#env.get(kname(n));
    if (c === undefined) return `${n} is not in the certificate`;
    if (c.kind !== kind) return `${n} is a ${c.kind} in the certificate, not a ${kind}`;
    if (c.levelParams.length !== 0) return `${n} is universe-polymorphic in the certificate`;
    return this.#tc.isDefEq(c.type, mine) ? true : `the certificate's ${n} has a different statement`;
  }

  #bind(n: string): true | string {
    const own = this.#own.get(n);
    if (own === undefined) return `${n} is not part of the project`;
    if (own.error !== undefined) return `${n}: ${own.error}`;
    const d = own.decl!;
    const used: Expr[] = [];
    if (d.k === "theorem") {
      const t = this.#elaborator().signature(d);
      const r = this.#sameType(n, t, "theorem");
      if (r !== true) return r;
      used.push(t);
    } else if (d.k === "def") {
      const t = this.#elaborator().signature(d);
      const r = this.#sameType(n, t, "definition");
      if (r !== true) return r;
      const eqn = this.#own.get(`${n}.ps_eqn`);
      if (eqn?.decl === undefined || eqn.decl.k !== "theorem") return `${n} has no equation`;
      const e = this.#elaborator().signature(eqn.decl);
      const re = this.#sameType(`${n}.ps_eqn`, e, "theorem");
      if (re !== true) return re;
      // Recursive if the body (the equation's right side) mentions the function.
      let body: Expr = e;
      while (body.kind === "pi") body = body.body;
      const rhs = body.kind === "app" ? body.arg : body;
      const self = new Set<Name>();
      constantsOf([rhs], self);
      used.push(t, e);
      if (self.has(kname(n))) {
        // The equation determines a recursive function only if it terminates: shown by its
        // uniqueness theorem, when Lean could prove it. Otherwise it stays an assumption.
        const uq = this.#own.get(`${n}.ps_unique`);
        let bound = false;
        if (uq?.decl !== undefined && uq.decl.k === "theorem") {
          try {
            const u = this.#elaborator().signature(uq.decl);
            if (this.#sameType(`${n}.ps_unique`, u, "theorem") === true) {
              used.push(u);
              bound = true;
            }
          } catch (err) {
            if (!(err instanceof ElabError || err instanceof KernelError)) throw err;
          }
        }
        if (!bound) this.recursive.add(n);
      }
    } else {
      const { type, ctors } = this.#elaborator().inductive(d);
      const c = this.#env.get(kname(n));
      if (c === undefined || c.kind !== "inductive") return `${n} is not an inductive type in the certificate`;
      if (c.levelParams.length !== 0 || c.numParams !== d.binders.length) return `the certificate's ${n} has different parameters`;
      if (!this.#tc.isDefEq(c.type, type)) return `the certificate's ${n} has a different type`;
      if (c.ctors.length !== ctors.length || c.ctors.some((x, i) => nameToString(x) !== ctors[i]!.name)) return `the certificate's ${n} has different constructors`;
      for (const ct of ctors) {
        const r = this.#sameType(ct.name, ct.type, "constructor");
        if (r !== true) return r;
      }
      used.push(type, ...ctors.map((x) => x.type));
    }
    // Everything the elaborated statements mention must be bound or authentic too.
    const deps = new Set<Name>();
    constantsOf(used, deps);
    for (const dn of deps) {
      if (dn === HOLE) continue;
      const r = this.#dependency(dn);
      if (r !== true) return `${n} depends on ${r}`;
    }
    return true;
  }

  #dependency(dn: Name): true | string {
    const s = nameToString(dn);
    if (this.#own.has(s)) {
      const r = this.bind(s);
      return r === true ? true : r;
    }
    const c = this.#env.get(dn);
    // Constructors and recursors of the project's inductive types.
    const ind = c?.kind === "constructor" ? nameToString(c.induct) : c?.kind === "recursor" ? nameToString(c.all[0]!) : undefined;
    if (ind !== undefined && this.#own.has(ind)) return this.bind(ind);
    const bad = authenticate(this.#env, [dn], () => false, this.#hasher, this.#libOk);
    return bad === undefined ? true : `${bad}, which is not the pinned Lean library's`;
  }

  /** Whether an axiom in a footprint is the pinned library's. */
  authenticAxiom(n: string): boolean {
    return authenticate(this.#env, [kname(n)], () => false, this.#hasher, this.#libOk) === undefined;
  }
}

// ---- Replay -----------------------------------------------------------------------------------

/** Checks `project` against a certificate, without Lean. */
export function checkWithCertificate(project: Project, certPath: string): CheckResult {
  const files = project.program.getSourceFiles().filter((f) => !f.isDeclarationFile && !/node_modules/.test(f.fileName));
  const tr = new Translator(project);
  const { decls: plain, diagnostics, unverified } = tr.translateFiles(files);
  const decls = withEquations(plain);
  const pos = (d: GeneratedDecl) => tr.diag(d.node, "");
  const theorems = decls.filter((d) => d.kind === "theorem" && d.aux === undefined);
  const base = (t: GeneratedDecl) => {
    const p = pos(t);
    return { tsName: t.tsName, file: p.file, line: p.line, leanName: t.leanName };
  };
  const notChecked = (t: GeneratedDecl): TheoremResult => ({ ...base(t), status: "failed", axioms: [], reflected: [], assumptions: [] });

  let header: CertificateHeader;
  let exportText: string;
  try {
    ({ header, exportText } = readCertificate(certPath));
  } catch (e) {
    diagnostics.push({ file: "", line: 0, column: 0, message: `cannot read the certificate: ${(e as Error).message}` });
    return { diagnostics, unverified, theorems: theorems.map(notChecked), declarationsChecked: 0 };
  }
  if (header.toolchain !== LEAN_TOOLCHAIN || libraryTable().toolchain !== LEAN_TOOLCHAIN) {
    diagnostics.push({ file: "", line: 0, column: 0, message: `the certificate was made with ${header.toolchain}; this ProofScript uses ${LEAN_TOOLCHAIN}: check with Lean to make a new one` });
    return { diagnostics, unverified, theorems: theorems.map(notChecked), declarationsChecked: 0 };
  }

  // 1. The kernel checks everything in the certificate.
  const kernel = new Kernel();
  let count = 0;
  try {
    for (const d of parseExport(exportText).declarations) {
      kernel.add(d);
      count++;
    }
    kernel.finish();
  } catch (e) {
    if (!(e instanceof KernelError)) throw e;
    diagnostics.push({ file: "", line: 0, column: 0, message: `the ProofScript kernel rejected the certificate: ${e.message}` });
    return { diagnostics, unverified, theorems: theorems.map(notChecked), declarationsChecked: count };
  }

  // 2. Bind every declaration of the project to the certificate's.
  const binder = new Binder(kernel, decls);
  const needsLean = (d: GeneratedDecl, why: string): Diagnostic => ({ ...pos(d), message: `${d.kind === "def" ? "definition" : d.kind === "inductive" ? "type" : "theorem"} ${d.tsName} is not covered by the certificate (${why}); check with Lean` });
  for (const d of decls) {
    if (d.kind === "theorem") continue;
    const r = binder.bind(d.leanName);
    if (r !== true) diagnostics.push(needsLean(d, r));
  }

  // 3. Results, with the same trust footprints as a check with Lean.
  const defNames = new Map(plain.filter((d) => d.kind === "def").map((d) => [d.leanName, d.tsName]));
  const defAssumptions = new Map(plain.filter((d) => d.kind === "def").map((d) => [d.leanName, d.assumptions ?? []]));
  const results = theorems.map((t): TheoremResult => {
    const r = binder.bind(t.leanName);
    if (r !== true) {
      diagnostics.push(needsLean(t, r));
      return notChecked(t);
    }
    const c = kernel.env.get(kname(t.leanName))!;
    const { axioms, reflected, leanDefs } = footprint(kernel, c, defNames);
    const forged = axioms.filter((a) => a !== "sorry" && STANDARD_AXIOMS.has(a) && !binder.authenticAxiom(a));
    if (forged.length > 0) {
      diagnostics.push({ ...pos(t), message: `the certificate's ${forged.join(", ")} is not Lean's axiom` });
      return notChecked(t);
    }
    const assumptions = new Set(leanDefs.flatMap((d) => defAssumptions.get(d) ?? []));
    const rec = leanDefs.filter((d) => binder.recursive.has(d)).map((d) => defNames.get(d)!);
    for (const f of rec) assumptions.add(`${f} terminates (proved by Lean when the certificate was made)`);
    return { ...base(t), status: axioms.includes("sorry") ? "admitted" : "verified", axioms, reflected, assumptions: [...assumptions].sort() };
  });
  return { diagnostics, unverified, theorems: results, declarationsChecked: count };
}
