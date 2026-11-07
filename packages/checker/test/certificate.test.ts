// Proof certificates: checking without Lean, and red-team cases that must never verify.
//
// Tests marked `hasLean` make certificates (and forgeries of them) with Lean; the others
// replay the committed certificate of examples/math and need only Node.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cpSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { gunzipSync, gzipSync } from "node:zlib";
import { Kernel, name as kname, parseExport } from "@proofscript/kernel";
import { checkWithCertificate, equationDecl, readCertificate, splitDef, writeCertificate } from "../src/certificate.ts";
import { type CheckResult, check } from "../src/check.ts";
import { exportDecls, leanAvailable, leanEnv } from "../src/lean.ts";
import { Hasher, authenticate } from "../src/library.ts";
import { loadProject } from "../src/project.ts";

const here = new URL(".", import.meta.url).pathname;
const fixtures = join(here, "fixtures");
const tmp = join(here, ".tmp");
const mathDir = new URL("../../../examples/math/", import.meta.url).pathname;
const hasLean = leanAvailable();

/** A copy of a project inside the repository (so that `proofscript` resolves). */
function copy(from: string, name: string): string {
  const dir = join(tmp, name);
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(tmp, { recursive: true });
  cpSync(from, dir, { recursive: true, filter: (s) => !/\.proofscript|proofscript\.cert$/.test(s) });
  return dir;
}

const replay = (dir: string, cert = join(dir, "proofscript.cert")): CheckResult => checkWithCertificate(loadProject(join(dir, "tsconfig.json")), cert);
const statuses = (r: CheckResult) => new Map(r.theorems.map((t) => [t.tsName, t.status]));

/**
 * A forged certificate: the project's generated Lean, edited, built and exported by Lean
 * itself (what an attacker who controls the certificate can produce).
 */
function forge(fixture: string, edit: (lean: string) => string): string {
  const dir = copy(join(fixtures, fixture), `forge-${fixture}-${Math.random().toString(36).slice(2, 8)}`);
  const r = check(join(dir, "tsconfig.json"), { writeCertificate: join(dir, "proofscript.cert") });
  assert.ok(r.theorems.every((t) => t.status === "verified"), "the honest certificate verifies");
  const work = join(dir, ".proofscript", "lean");
  const src = edit(readFileSync(join(work, "PSGen.lean"), "utf8"));
  writeFileSync(join(work, "PSGen.lean"), src);
  const b = spawnSync("lake", ["build"], { cwd: work, env: leanEnv(), encoding: "utf8" });
  assert.equal(b.status, 0, `the forgery builds:\n${b.stdout}`);
  const names = [...src.matchAll(/^(?:@\[simp\] )?(?:theorem|def|inductive) (\S+)/gm)].map((m) => m[1]!);
  writeCertificate(join(dir, "proofscript.cert"), exportDecls(work, names), []);
  return dir;
}

// ---- Without Lean ---------------------------------------------------------------------------

test("examples/math verifies from its committed certificate, without Lean", () => {
  const r = checkWithCertificate(loadProject(join(mathDir, "tsconfig.json")), join(mathDir, "proofscript.cert"));
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 28);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
  const rev = r.theorems.find((t) => t.tsName === "reverse_reverse")!;
  assert.ok(rev.reflected.includes("reverse"));
  assert.ok(rev.assumptions.some((a) => /terminate/.test(a)), "termination taken from the certificate is an assumption");
});

test("examples/tutorial verifies from its committed certificate, without Lean", () => {
  const dir = new URL("../../../examples/tutorial/", import.meta.url).pathname;
  const r = replay(dir);
  assert.deepEqual(r.diagnostics, []);
  assert.equal(r.theorems.length, 12);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
});

test("a changed statement is not covered by an old certificate", () => {
  const dir = copy(mathDir, "math-changed");
  const f = join(dir, "src", "nat.ts");
  const src = readFileSync(f, "utf8");
  // add_comm now claims multiplication commutes (true, but not what was proved).
  const changed = src.replace("prove(a + b === b + a,", "prove(a * b === b * a,");
  assert.notEqual(changed, src);
  writeFileSync(f, changed);
  const r = replay(dir, join(mathDir, "proofscript.cert"));
  const s = statuses(r);
  assert.equal(s.get("add_comm"), "failed");
  assert.ok(r.diagnostics.some((d) => /add_comm is not covered by the certificate \(.*different statement/.test(d.message)));
  assert.equal(s.get("mul_comm"), "verified", "unchanged theorems still verify");
});

test("a changed definition invalidates the theorems that depend on it", () => {
  const dir = copy(mathDir, "math-changed-def");
  const f = join(dir, "src", "list.ts");
  const src = readFileSync(f, "utf8");
  const changed = src.replace("1 + length(xs.tail)", "2 + length(xs.tail)");
  assert.notEqual(changed, src, "the fixture has the expected shape");
  writeFileSync(f, changed);
  const r = replay(dir, join(mathDir, "proofscript.cert"));
  const s = statuses(r);
  assert.equal(s.get("length_append"), "failed");
  assert.equal(s.get("append_assoc"), "verified", "theorems not about length are unaffected");
});

test("a new theorem needs Lean", () => {
  const dir = copy(mathDir, "math-new");
  const f = join(dir, "src", "nat.ts");
  writeFileSync(f, `${readFileSync(f, "utf8")}\nexport function zero_add(a: nat): Proof {\n  return prove(0 + a === a, omega);\n}\n`);
  const r = replay(dir, join(mathDir, "proofscript.cert"));
  assert.equal(statuses(r).get("zero_add"), "failed");
  assert.ok(r.diagnostics.some((d) => /zero_add.*not in the certificate/.test(d.message)));
});

test("a certificate from another toolchain is not used", () => {
  const dir = copy(mathDir, "math-toolchain");
  const { header, exportText } = readCertificate(join(mathDir, "proofscript.cert"));
  writeFileSync(join(dir, "proofscript.cert"), gzipSync(`${JSON.stringify({ ...header, toolchain: "leanprover/lean4:v4.0.0" })}\n${exportText}`));
  const r = replay(dir);
  assert.ok(r.theorems.every((t) => t.status !== "verified"));
  assert.ok(r.diagnostics.some((d) => /made with leanprover\/lean4:v4\.0\.0/.test(d.message)));
});

test("a corrupted proof is rejected by the kernel", () => {
  const dir = copy(mathDir, "math-corrupt");
  const text = gunzipSync(readFileSync(join(mathDir, "proofscript.cert"))).toString("utf8");
  // Point some application at a different argument: the export no longer type-checks.
  const lines = text.split("\n");
  const i = lines.findIndex((l, k) => k > lines.length / 2 && /^\{"app":\{"arg":\d+/.test(l));
  assert.ok(i > 0);
  lines[i] = lines[i]!.replace(/"arg":(\d+)/, (_, a) => `"arg":${Math.max(0, Number(a) - 7)}`);
  writeFileSync(join(dir, "proofscript.cert"), gzipSync(lines.join("\n")));
  const r = replay(dir);
  assert.ok(r.theorems.every((t) => t.status !== "verified"), "nothing verifies");
});

test("library constants are authenticated: a redefined Nat.add is detected", () => {
  const { exportText } = readCertificate(join(mathDir, "proofscript.cert"));
  const k = new Kernel();
  for (const d of parseExport(exportText).declarations) k.add(d);
  k.finish();
  const hasher = new Hasher();
  assert.equal(authenticate(k.env, [kname("instHAdd"), kname("instAddNat")], () => false, hasher, new Set()), undefined, "the real library is authentic");
  // An environment in which Nat.add means multiplication (the point is that authentication,
  // not the kernel, catches it).
  const real = k.env.get(kname("Nat.add"))!;
  const other = k.env.get(kname("Nat.mul"))!;
  assert.ok(real.kind === "definition" && other.kind === "definition");
  const fake = { ...real, value: other.value };
  const shadow = { get: (n: typeof real.name) => (n === real.name ? fake : k.env.get(n)) } as unknown as typeof k.env;
  assert.equal(authenticate(shadow, [kname("instAddNat")], () => false, new Hasher(), new Set()), "Nat.add");
});

test("definition equations: binders lose their tactic defaults, the body is kept", () => {
  const src = "def PS.m.f (a : (Array Nat)) (i : Nat) (pre_0 : i < (a).size := by first | omega | (simp_all <;> omega)) : Nat :=\n  (a[i]'(by omega))\ntermination_by i";
  const parts = splitDef(src)!;
  assert.equal(parts.name, "PS.m.f");
  assert.deepEqual(parts.binders.length, 3);
  assert.equal(parts.body, "  (a[i]'(by omega))");
  const eqn = equationDecl({ kind: "def", tsName: "f", leanName: "PS.m.f", node: {} as never, source: src, deps: new Set() })!;
  assert.match(eqn.source, /^theorem PS\.m\.f\.ps_eqn \(a : \(Array Nat\)\) \(i : Nat\) \(pre_0 : i < \(a\)\.size\) :\n    PS\.m\.f a i pre_0 = \(\n  \(a\[i\]'\(by omega\)\)\) :=/);
});

// ---- Forgeries (made with Lean) --------------------------------------------------------------

test("forged: a theorem proved with a weaker statement", { skip: !hasLean }, () => {
  const dir = forge("good-nat", (s) => s.replace(/(theorem PS\.nat\.add_comm \(a : Nat\) \(b : Nat\) :\n {4})[^\n]*(\s*:=\s*\n\s*by\s*\n\s*omega)/, "$1True :=\n  by\n    trivial"));
  const r = replay(dir);
  assert.equal(statuses(r).get("add_comm"), "failed");
  assert.ok(r.diagnostics.some((d) => /different statement/.test(d.message)));
});

/** Replaces the generated declaration starting with `head` (blocks are separated by blank lines). */
function replaceDecl(src: string, head: string, f: (block: string) => string): string {
  const blocks = src.split("\n\n");
  const i = blocks.findIndex((b) => b.startsWith(head));
  assert.ok(i >= 0, `no declaration ${head}`);
  blocks[i] = f(blocks[i]!);
  return blocks.join("\n\n");
}

test("forged: a definition that means something else, with a consistent equation", { skip: !hasLean }, () => {
  // `double n` is `n`: definition, equation and theorem agree, and Lean accepts them all.
  // The equation no longer matches the TypeScript.
  const dir = forge("good-nat", (s) => {
    s = replaceDecl(s, "def PS.nat.double ", (b) => `${b.slice(0, b.indexOf(":=\n") + 3)}  n`);
    return replaceDecl(s, "theorem PS.nat.double.ps_eqn", (b) => `${b.slice(0, b.indexOf("= (\n") + 4)}  n) :=\n  by rfl`);
  });
  const r = replay(dir);
  assert.equal(statuses(r).get("double_ge"), "failed");
  assert.ok(r.diagnostics.some((d) => /definition double is not covered/.test(d.message)));
});

test("forged: an inductive type with an extra constructor", { skip: !hasLean }, () => {
  const dir = forge("good-list", (s) =>
    s
      .replace("  | leaf : PS.list.Tree\n", "  | leaf : PS.list.Tree\n  | extra : PS.list.Tree\n")
      .replace(/ {2}\| \.leaf =>\n {4}(\S+)\n/g, "  | .leaf =>\n    $1\n  | .extra =>\n    $1\n")
      .replace(/( {4}\| leaf =>\n {6}([^\n]+)\n)/, "$1    | extra =>\n      $2\n"),
  );
  const r = replay(dir);
  assert.ok(r.theorems.every((t) => t.status !== "verified"));
  assert.ok(r.diagnostics.some((d) => /different constructors/.test(d.message)));
});

test("forged: a proof replaced by sorry is admitted, never verified", { skip: !hasLean }, () => {
  const dir = forge("good-nat", (s) => s.replace(/(theorem PS\.nat\.add_comm[^]*?:=\s*\n\s*by\s*\n\s*)omega/, "$1sorry"));
  const r = replay(dir);
  assert.equal(statuses(r).get("add_comm"), "admitted");
});

test("every good fixture replays from its own certificate", { skip: !hasLean }, () => {
  for (const name of ["good-loop", "good-mutation", "good-indexed", "good-string", "good-struct", "good-overflow"]) {
    const dir = copy(join(fixtures, name), `roundtrip-${name}`);
    const r1 = check(join(dir, "tsconfig.json"), { writeCertificate: join(dir, "proofscript.cert") });
    assert.ok(r1.theorems.every((t) => t.status === "verified"), name);
    const r2 = replay(dir);
    assert.deepEqual(r2.diagnostics, [], name);
    assert.deepEqual([...statuses(r2)], [...statuses(r1)], name);
  }
});
