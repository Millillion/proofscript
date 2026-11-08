// `proofscript check`: translate, prove with Lean (untrusted), check with the kernel.

import { join, relative } from "node:path";
import { type ConstantInfo, type Expr, Kernel, KernelError, type Name, name as kname, nameToString, parseExport } from "@proofscript/kernel";
import { withEquations, writeCertificate } from "./certificate.ts";
import { buildLean, exportDecls } from "./lean.ts";
import { type Project, loadProject } from "./project.ts";
import { type Diagnostic, type GeneratedDecl, Translator } from "./translate.ts";

export interface TheoremResult {
  readonly tsName: string;
  readonly file: string;
  readonly line: number;
  readonly leanName: string;
  /** `admitted`: checked, but depends on `sorry`. */
  readonly status: "verified" | "admitted" | "failed";
  /** Axioms the proof depends on (its trust footprint). */
  readonly axioms: string[];
  /** TypeScript functions reflected into the logic that the result depends on (trusted translation). */
  readonly reflected: string[];
  /** Environment assumptions those translations rely on (D32). */
  readonly assumptions: string[];
}

export interface CheckResult {
  readonly diagnostics: Diagnostic[];
  readonly unverified: Diagnostic[];
  readonly theorems: TheoremResult[];
  readonly declarationsChecked: number;
}

/** Axioms of Lean's logic that ProofScript accepts as standard (design §6.7). */
export const STANDARD_AXIOMS = new Set(["propext", "Quot.sound", "Classical.choice"]);

export interface CheckOptions {
  /** Where Lean builds (default: `.proofscript/lean` in the project). */
  readonly workDir?: string;
  /** Write a certificate of the checked declarations here (see certificate.ts). */
  readonly writeCertificate?: string;
}

export function check(target: string | readonly string[], opts: CheckOptions = {}): CheckResult {
  const project = loadProject(target);
  return checkProject(project, opts.workDir ?? join(project.rootDir, ".proofscript", "lean"), opts);
}

/** `PROOFSCRIPT_TIMING=1`: report how long each stage takes (on stderr). */
function stage(name: string, t0: number): number {
  const t = Date.now();
  if (process.env.PROOFSCRIPT_TIMING !== undefined) console.error(`[timing] ${name}: ${((t - t0) / 1000).toFixed(1)}s`);
  return t;
}

export function checkProject(project: Project, workDir: string, opts: CheckOptions = {}): CheckResult {
  let t = Date.now();
  const files = project.program.getSourceFiles().filter((f) => !f.isDeclarationFile && !/node_modules/.test(f.fileName));
  const tr = new Translator(project);
  const translation = tr.translateFiles(files);
  const { diagnostics, unverified } = translation;
  // A certificate binds definitions by their equations, which Lean must prove too.
  const decls = opts.writeCertificate === undefined ? translation.decls : withEquations(translation.decls);
  const theorems = decls.filter((d) => d.kind === "theorem" && d.aux === undefined);
  const pos = (d: GeneratedDecl) => tr.diag(d.node, "");
  // Declarations that could not be translated are reported; everything else is still checked.
  // Definitions carry obligations of their own (bounds, preconditions, overflow), so they are
  // checked even when there are no theorems.
  if (decls.length === 0) return { diagnostics, unverified, theorems: [], declarationsChecked: 0 };

  t = stage("translate", t);
  // 1. Prove with Lean (untrusted).
  let build = buildLean(workDir, decls);
  t = stage("lean", t);
  const failed = new Set<GeneratedDecl>();
  if (!build.ok) {
    const starts = [...build.lines.entries()].sort((a, b) => a[1] - b[1]);
    for (const m of build.messages) {
      if (m.severity !== "error") continue;
      let owner = starts[0]?.[0];
      for (const [d, line] of starts) if (line <= m.line) owner = d;
      if (owner === undefined) continue;
      failed.add(owner);
      // An equation that Lean cannot prove only leaves its definition out of the certificate.
      if (owner.aux !== undefined) continue;
      const p = pos(owner);
      diagnostics.push({ ...p, message: explain(owner, m.text) });
    }
    // Drop what failed (and everything depending on it), and check the rest.
    const byName = new Map(decls.map((d) => [d.leanName, d]));
    const dead = new Set<GeneratedDecl>(failed);
    for (let changed = true; changed; ) {
      changed = false;
      for (const d of decls) {
        if (!dead.has(d) && [...d.deps].some((n) => byName.has(n) && dead.has(byName.get(n)!))) {
          dead.add(d);
          changed = true;
        }
      }
    }
    for (const d of dead) failed.add(d);
    const alive = decls.filter((d) => !dead.has(d));
    const failedResults = theorems.filter((t) => dead.has(t)).map((t) => ({ ...base(t, pos), status: "failed" as const, axioms: [], reflected: [], assumptions: [] }));
    if (alive.length === 0) return { diagnostics, unverified, theorems: failedResults, declarationsChecked: 0 };
    build = buildLean(workDir, alive);
    t = stage("lean (second pass)", t);
    if (!build.ok) {
      diagnostics.push({ file: "", line: 0, column: 0, message: "Lean failed on declarations that did not fail on their own; nothing could be checked" });
      return { diagnostics, unverified, theorems: theorems.map((t) => ({ ...base(t, pos), status: "failed" as const, axioms: [], reflected: [], assumptions: [] })), declarationsChecked: 0 };
    }
  }

  // 2. Export the proofs and check them with ProofScript's kernel (trusted).
  // Every surviving definition and theorem goes through the kernel.
  const checked = decls.filter((d) => !failed.has(d));
  const text = exportDecls(workDir, checked.map((d) => d.leanName));
  t = stage(`export (${(text.length / 1e6).toFixed(1)} MB)`, t);
  const kernel = new Kernel();
  let count = 0;
  try {
    for (const d of parseExport(text).declarations) {
      kernel.add(d);
      count++;
    }
    kernel.finish();
    t = stage("kernel", t);
  } catch (e) {
    if (!(e instanceof KernelError)) throw e;
    diagnostics.push({ file: "", line: 0, column: 0, message: `the ProofScript kernel rejected the proof terms Lean produced: ${e.message}` });
    return { diagnostics, unverified, theorems: theorems.map((t) => ({ ...base(t, pos), status: "failed" as const, axioms: [], reflected: [], assumptions: [] })), declarationsChecked: count };
  }

  if (opts.writeCertificate !== undefined) writeCertificate(opts.writeCertificate, text, checked.filter((d) => d.kind === "theorem" && d.aux === undefined).map((d) => d.leanName));

  const defNames = new Map(decls.filter((d) => d.kind === "def").map((d) => [d.leanName, d.tsName]));
  const defAssumptions = new Map(decls.filter((d) => d.kind === "def").map((d) => [d.leanName, d.assumptions ?? []]));
  const results = theorems.map((t) => {
    if (failed.has(t)) return { ...base(t, pos), status: "failed" as const, axioms: [], reflected: [], assumptions: [] };
    const c = kernel.env.get(kname(t.leanName));
    if (c === undefined || c.kind !== "theorem") {
      diagnostics.push({ ...pos(t), message: `internal error: ${t.leanName} missing from the export` });
      return { ...base(t, pos), status: "failed" as const, axioms: [], reflected: [], assumptions: [] };
    }
    const { axioms, reflected, leanDefs } = footprint(kernel, c, defNames);
    const assumptions = [...new Set(leanDefs.flatMap((d) => defAssumptions.get(d) ?? []))].sort();
    return { ...base(t, pos), status: axioms.includes("sorry") ? ("admitted" as const) : ("verified" as const), axioms, reflected, assumptions };
  });
  return { diagnostics, unverified, theorems: results, declarationsChecked: count };
}

/** Plain-language explanations of the Lean failures ProofScript's translation can produce. */
export function explain(owner: GeneratedDecl, text: string): string {
  const detail = text.split("\n").slice(0, 12).join("\n");
  const m = /could not synthesize default value for parameter '(inv|pre)_(\d+)/.exec(text);
  if (m !== null) {
    return m[1] === "inv"
      ? `loop invariant #${Number(m[2]) + 1} of ${owner.tsName} may not hold (on entry to the loop, or after an iteration)`
      : `a precondition may not hold at a call in ${owner.tsName}`;
  }
  if (/failed to prove index is valid/.test(text)) return `an array index in ${owner.tsName} may be out of bounds (JavaScript would read \`undefined\`)`;
  if (/fail to show termination|failed to prove termination/.test(text)) {
    return `${owner.tsName} may not terminate: give the loop a measure with \`e satisfies Decreases;\` that decreases on every iteration`;
  }
  if (/Expected type must not contain free variables/.test(text)) return `a side condition in ${owner.tsName} could not be proved`;
  if (owner.kind === "theorem") return `proof failed: ${detail}`;
  return `could not translate ${owner.tsName} to the logic: ${detail}`;
}

function base(t: GeneratedDecl, pos: (d: GeneratedDecl) => Diagnostic) {
  const p = pos(t);
  return { tsName: t.tsName, file: p.file, line: p.line, leanName: t.leanName };
}

/** The constants a constant mentions directly, computed once per constant (shared subterms once). */
const directDeps = new WeakMap<ConstantInfo, readonly Name[]>();
function depsOf(c: ConstantInfo): readonly Name[] {
  const hit = directDeps.get(c);
  if (hit !== undefined) return hit;
  const out = new Set<Name>();
  const seen = new Set<Expr>();
  const stack: Expr[] = [c.type];
  if ("value" in c) stack.push(c.value);
  if (c.kind === "recursor") for (const r of c.rules) stack.push(r.rhs);
  while (stack.length > 0) {
    const e = stack.pop()!;
    if (seen.has(e)) continue;
    seen.add(e);
    switch (e.kind) {
      case "const":
        out.add(e.name);
        break;
      case "app":
        stack.push(e.fn, e.arg);
        break;
      case "lam":
      case "pi":
        stack.push(e.binderType, e.body);
        break;
      case "let":
        stack.push(e.binderType, e.value, e.body);
        break;
      case "proj":
        stack.push(e.struct);
        break;
      default:
        break;
    }
  }
  const r = [...out];
  directDeps.set(c, r);
  return r;
}

/** Transitive axioms (Lean's `#print axioms`) and reflected TypeScript functions a constant depends on. */
export function footprint(
  kernel: Kernel,
  root: ConstantInfo,
  defNames: ReadonlyMap<string, string>,
): { axioms: string[]; reflected: string[]; leanDefs: string[] } {
  const seen = new Set<Name>([root.name]);
  const axioms = new Set<string>();
  const reflected = new Set<string>();
  const leanDefs = new Set<string>();
  const stack: ConstantInfo[] = [root];
  while (stack.length > 0) {
    const c = stack.pop()!;
    const cn = nameToString(c.name);
    const ts = defNames.get(cn);
    if (ts !== undefined) {
      reflected.add(ts);
      leanDefs.add(cn);
    }
    if (c.kind === "axiom") axioms.add(cn === "sorryAx" ? "sorry" : cn);
    for (const d of depsOf(c)) {
      if (seen.has(d)) continue;
      seen.add(d);
      const dc = kernel.env.get(d);
      if (dc !== undefined) stack.push(dc);
    }
  }
  return { axioms: [...axioms].sort(), reflected: [...reflected].sort(), leanDefs: [...leanDefs] };
}

export function formatResult(r: CheckResult, rootDir: string): string {
  const lines: string[] = [];
  for (const d of r.diagnostics) {
    const where = d.file === "" ? "" : `${relative(rootDir, d.file)}:${d.line}:${d.column}: `;
    lines.push(`${where}error: ${d.message}`);
  }
  for (const d of r.unverified) lines.push(`${relative(rootDir, d.file)}:${d.line}:${d.column}: warning: ${d.message}`);
  for (const t of r.theorems) {
    const extra = t.axioms.filter((a) => !STANDARD_AXIOMS.has(a));
    const mark = t.status === "verified" ? (extra.length > 0 ? "⚠" : "✓") : t.status === "admitted" ? "⚠" : "✗";
    const ax = (t.axioms.length === 0 ? "no axioms" : `axioms: ${t.axioms.join(", ")}`) + (t.reflected.length === 0 ? "" : `; trusts the translation of ${t.reflected.join(", ")}`) + (t.assumptions.length === 0 ? "" : `; assumes ${t.assumptions.join(", ")}`);
    lines.push(`${mark} ${t.tsName} (${relative(rootDir, t.file)}:${t.line}) — ${t.status}, ${ax}`);
  }
  const verified = r.theorems.filter((t) => t.status === "verified").length;
  lines.push(
    `\n${verified}/${r.theorems.length} theorems verified; ${r.declarationsChecked} declarations checked by the ProofScript kernel.`,
  );
  return lines.join("\n");
}
