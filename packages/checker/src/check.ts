// `proofscript check`: translate, prove with Lean (untrusted), check with the kernel.

import { join, relative } from "node:path";
import { type ConstantInfo, type Expr, Kernel, KernelError, name as kname, nameToString, parseExport, visit } from "@proofscript/kernel";
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
}

export interface CheckResult {
  readonly diagnostics: Diagnostic[];
  readonly unverified: Diagnostic[];
  readonly theorems: TheoremResult[];
  readonly declarationsChecked: number;
}

/** Axioms of Lean's logic that ProofScript accepts as standard (design §6.7). */
export const STANDARD_AXIOMS = new Set(["propext", "Quot.sound", "Classical.choice"]);

export function check(target: string | readonly string[], workDir?: string): CheckResult {
  const project = loadProject(target);
  return checkProject(project, workDir ?? join(project.rootDir, ".proofscript", "lean"));
}

export function checkProject(project: Project, workDir: string): CheckResult {
  const files = project.program.getSourceFiles().filter((f) => !f.isDeclarationFile && !/node_modules/.test(f.fileName));
  const tr = new Translator(project);
  const { decls, diagnostics, unverified } = tr.translateFiles(files);
  const theorems = decls.filter((d) => d.kind === "theorem");
  const pos = (d: GeneratedDecl) => tr.diag(d.node, "");
  // Declarations that could not be translated are reported; everything else is still checked.
  if (theorems.length === 0) return { diagnostics, unverified, theorems: [], declarationsChecked: 0 };

  // 1. Prove with Lean (untrusted).
  const build = buildLean(workDir, decls);
  const failed = new Set<GeneratedDecl>();
  if (!build.ok) {
    const starts = [...build.lines.entries()].sort((a, b) => a[1] - b[1]);
    for (const m of build.messages) {
      if (m.severity !== "error") continue;
      let owner = starts[0]?.[0];
      for (const [d, line] of starts) if (line <= m.line) owner = d;
      if (owner === undefined) continue;
      failed.add(owner);
      const p = pos(owner);
      const what = owner.kind === "theorem" ? "proof failed" : `could not translate ${owner.tsName} to the logic`;
      diagnostics.push({ ...p, message: `${what}: ${m.text}` });
    }
    return {
      diagnostics,
      unverified,
      theorems: theorems.map((t) => ({ ...base(t, pos), status: "failed" as const, axioms: [], reflected: [] })),
      declarationsChecked: 0,
    };
  }

  // 2. Export the proofs and check them with ProofScript's kernel (trusted).
  const text = exportDecls(workDir, theorems.map((t) => t.leanName));
  const kernel = new Kernel();
  let count = 0;
  try {
    for (const d of parseExport(text).declarations) {
      kernel.add(d);
      count++;
    }
    kernel.finish();
  } catch (e) {
    if (!(e instanceof KernelError)) throw e;
    diagnostics.push({ file: "", line: 0, column: 0, message: `the ProofScript kernel rejected the proof terms Lean produced: ${e.message}` });
    return { diagnostics, unverified, theorems: theorems.map((t) => ({ ...base(t, pos), status: "failed" as const, axioms: [], reflected: [] })), declarationsChecked: count };
  }

  const defNames = new Map(decls.filter((d) => d.kind === "def").map((d) => [d.leanName, d.tsName]));
  const results = theorems.map((t) => {
    const c = kernel.env.get(kname(t.leanName));
    if (c === undefined || c.kind !== "theorem") {
      diagnostics.push({ ...pos(t), message: `internal error: ${t.leanName} missing from the export` });
      return { ...base(t, pos), status: "failed" as const, axioms: [], reflected: [] };
    }
    const { axioms, reflected } = footprint(kernel, c, defNames);
    return { ...base(t, pos), status: axioms.includes("sorry") ? ("admitted" as const) : ("verified" as const), axioms, reflected };
  });
  return { diagnostics, unverified, theorems: results, declarationsChecked: count };
}

function base(t: GeneratedDecl, pos: (d: GeneratedDecl) => Diagnostic) {
  const p = pos(t);
  return { tsName: t.tsName, file: p.file, line: p.line, leanName: t.leanName };
}

/** Transitive axioms (Lean's `#print axioms`) and reflected TypeScript functions a constant depends on. */
export function footprint(kernel: Kernel, root: ConstantInfo, defNames: ReadonlyMap<string, string>): { axioms: string[]; reflected: string[] } {
  const seen = new Set<string>();
  const axioms = new Set<string>();
  const stack: ConstantInfo[] = [root];
  const push = (e: Expr) =>
    visit(e, (s) => {
      if (s.kind === "const") {
        const n = nameToString(s.name);
        if (!seen.has(n)) {
          seen.add(n);
          const c = kernel.env.get(s.name);
          if (c !== undefined) stack.push(c);
        }
        return false;
      }
      return true;
    });
  const reflected = new Set<string>();
  while (stack.length > 0) {
    const c = stack.pop()!;
    const cn = nameToString(c.name);
    const ts = defNames.get(cn);
    if (ts !== undefined) reflected.add(ts);
    if (c.kind === "axiom") axioms.add(cn === "sorryAx" ? "sorry" : cn);
    push(c.type);
    if ("value" in c) push(c.value);
    if (c.kind === "recursor") for (const r of c.rules) push(r.rhs);
  }
  return { axioms: [...axioms].sort(), reflected: [...reflected].sort() };
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
    const ax = (t.axioms.length === 0 ? "no axioms" : `axioms: ${t.axioms.join(", ")}`) + (t.reflected.length === 0 ? "" : `; trusts the translation of ${t.reflected.join(", ")}`);
    lines.push(`${mark} ${t.tsName} (${relative(rootDir, t.file)}:${t.line}) — ${t.status}, ${ax}`);
  }
  const verified = r.theorems.filter((t) => t.status === "verified").length;
  lines.push(
    `\n${verified}/${r.theorems.length} theorems verified; ${r.declarationsChecked} declarations checked by the ProofScript kernel.`,
  );
  return lines.join("\n");
}
