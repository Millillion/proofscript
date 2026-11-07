// `proofscript audit`: what a project's verification rests on.
//
// A check says which theorems verified. An audit adds what each result trusts, collected
// over the whole project: the axioms, the TypeScript functions whose translation is trusted,
// the environment assumptions, and the boundary between verified and unverified code
// (preconditions that nothing proves, because the caller is not verified code).

import { relative } from "node:path";
import ts from "typescript6";
import { type CheckResult, STANDARD_AXIOMS } from "./check.ts";
import type { Project } from "./project.ts";
import { Translator } from "./translate.ts";

export interface BoundaryItem {
  readonly file: string;
  readonly line: number;
  readonly column: number;
  /** `call`: a call from unverified code; `export`: callers outside the project. */
  readonly kind: "call" | "export";
  readonly fn: string;
  readonly message: string;
}

export interface Audit {
  readonly mode: "lean" | "certificate";
  readonly result: CheckResult;
  /** Each axiom, assumption and trusted translation, with the theorems that depend on it. */
  readonly axioms: Readonly<Record<string, string[]>>;
  readonly reflected: Readonly<Record<string, string[]>>;
  readonly assumptions: Readonly<Record<string, string[]>>;
  readonly boundary: readonly BoundaryItem[];
  /** The components every result trusts. */
  readonly trustedBase: readonly string[];
}

function group(result: CheckResult, pick: (t: CheckResult["theorems"][number]) => readonly string[]): Record<string, string[]> {
  const out: Record<string, string[]> = {};
  for (const t of result.theorems) {
    if (t.status === "failed") continue;
    for (const k of pick(t)) (out[k] ??= []).push(t.tsName);
  }
  return Object.fromEntries(Object.entries(out).sort(([a], [b]) => (a < b ? -1 : 1)));
}

/** The function-like declaration whose body contains `n` (as the translator keys them). */
function enclosingFunction(n: ts.Node): ts.Node | undefined {
  for (let p: ts.Node | undefined = n.parent; p !== undefined; p = p.parent) {
    if (ts.isFunctionDeclaration(p) || ts.isMethodDeclaration(p)) return p;
    if ((ts.isArrowFunction(p) || ts.isFunctionExpression(p)) && ts.isVariableDeclaration(p.parent)) return p.parent;
    if (ts.isArrowFunction(p) || ts.isFunctionExpression(p)) return p;
  }
  return undefined;
}

/** Calls of functions with preconditions from code that is not verified, and exported such functions. */
export function boundary(project: Project): BoundaryItem[] {
  const files = project.program.getSourceFiles().filter((f) => !f.isDeclarationFile && !/node_modules/.test(f.fileName));
  const tr = new Translator(project);
  tr.translateFiles(files);
  const verified = new Set(tr.decls.keys());
  const withPre = new Map<ts.Node, string>();
  const out: BoundaryItem[] = [];
  const at = (node: ts.Node) => {
    const sf = node.getSourceFile();
    const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    return { file: sf.fileName, line: line + 1, column: character + 1 };
  };
  for (const [node, d] of tr.decls) {
    if (d.kind !== "def") continue;
    const params = ts.isFunctionDeclaration(node)
      ? node.parameters
      : ts.isVariableDeclaration(node) && node.initializer !== undefined && (ts.isArrowFunction(node.initializer) || ts.isFunctionExpression(node.initializer))
        ? node.initializer.parameters
        : undefined;
    if (params === undefined || !tr.hasPreconditions(params)) continue;
    withPre.set(node, d.tsName);
    const exported = (ts.canHaveModifiers(node) ? ts.getModifiers(node) : ts.getModifiers(node.parent.parent as ts.VariableStatement))?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
    if (exported) {
      out.push({ ...at(node), kind: "export", fn: d.tsName, message: `${d.tsName} is exported: callers outside this project must establish its preconditions themselves` });
    }
  }
  const visit = (n: ts.Node): void => {
    if (ts.isCallExpression(n)) {
      const decl = tr.declOf(n.expression);
      const target = decl === undefined ? undefined : ts.isVariableDeclaration(decl) || ts.isFunctionDeclaration(decl) ? decl : undefined;
      const name = target === undefined ? undefined : withPre.get(target);
      if (name !== undefined) {
        const encl = enclosingFunction(n);
        if (encl === undefined || !verified.has(encl)) {
          const where = encl === undefined ? "top-level code" : "an unverified function";
          out.push({ ...at(n), kind: "call", fn: name, message: `call of ${name} from ${where}: its preconditions are not proved here` });
        }
      }
    }
    ts.forEachChild(n, visit);
  };
  for (const f of files) visit(f);
  return out.sort((a, b) => (a.file === b.file ? a.line - b.line : a.file < b.file ? -1 : 1));
}

export function audit(project: Project, result: CheckResult, mode: "lean" | "certificate"): Audit {
  const trustedBase = [
    "ProofScript's kernel (packages/kernel)",
    "the translation of TypeScript definitions into the logic (packages/checker/src/translate.ts)",
    ...(mode === "certificate" ? ["the statement elaborator (packages/checker/src/elab.ts) and the library hashes (library.json)"] : []),
  ];
  return {
    mode,
    result,
    axioms: group(result, (t) => t.axioms),
    reflected: group(result, (t) => t.reflected),
    assumptions: group(result, (t) => t.assumptions),
    boundary: boundary(project),
    trustedBase,
  };
}

export function formatAudit(a: Audit, rootDir: string): string {
  const r = a.result;
  const lines: string[] = [];
  const count = (s: string) => r.theorems.filter((t) => t.status === s).length;
  lines.push(`ProofScript audit (${a.mode === "certificate" ? "from a certificate, without Lean" : "proved with Lean"})`, "");
  lines.push(`Theorems: ${r.theorems.length} (${count("verified")} verified, ${count("admitted")} admitted, ${count("failed")} not verified)`);
  lines.push(`Kernel: ${r.declarationsChecked} declarations checked`);
  if (r.diagnostics.length > 0) lines.push(`Errors: ${r.diagnostics.length} (run \`proofscript check\` for details)`);
  const section = (title: string, m: Readonly<Record<string, string[]>>, note: (k: string) => string = () => "") => {
    lines.push("", title);
    const keys = Object.keys(m);
    if (keys.length === 0) lines.push("  (none)");
    for (const k of keys) lines.push(`  ${k}${note(k)} — ${m[k]!.length} theorem${m[k]!.length === 1 ? "" : "s"}: ${m[k]!.join(", ")}`);
  };
  section("Axioms", a.axioms, (k) => (k === "sorry" ? " (unproved: admitted)" : STANDARD_AXIOMS.has(k) ? " (standard)" : " (not standard)"));
  section("Trusted translations (TypeScript functions reflected into the logic)", a.reflected);
  section("Assumptions", a.assumptions);
  lines.push("", "Boundary (where verified code meets unverified code)");
  if (a.boundary.length === 0) lines.push("  (none)");
  for (const b of a.boundary) lines.push(`  ${relative(rootDir, b.file)}:${b.line}:${b.column}: ${b.message}`);
  lines.push("", "Unverified specifications");
  if (r.unverified.length === 0) lines.push("  (none)");
  for (const u of r.unverified) lines.push(`  ${relative(rootDir, u.file)}:${u.line}:${u.column}: ${u.message}`);
  lines.push("", "Trusted base");
  for (const t of a.trustedBase) lines.push(`  ${t}`);
  return lines.join("\n");
}

/** The audit as JSON (paths relative to the project). */
export function auditJson(a: Audit, rootDir: string): string {
  const rel = <T extends { file: string }>(x: T): T => ({ ...x, file: x.file === "" ? "" : relative(rootDir, x.file) });
  return JSON.stringify(
    {
      mode: a.mode,
      theorems: a.result.theorems.map(rel),
      diagnostics: a.result.diagnostics.map(rel),
      unverified: a.result.unverified.map(rel),
      declarationsChecked: a.result.declarationsChecked,
      axioms: a.axioms,
      reflected: a.reflected,
      assumptions: a.assumptions,
      boundary: a.boundary.map(rel),
      trustedBase: a.trustedBase,
    },
    null,
    2,
  );
}
