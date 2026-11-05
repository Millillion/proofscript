// Generates src/library.json: content hashes of the Lean library constants that certificate
// statements may depend on, and the binder kinds of those the elaborator applies.
//
// Needs Lean (the pinned toolchain). Run after changing LEAN_TOOLCHAIN or the elaborator's
// vocabulary:  node --stack-size=65500 packages/checker/scripts/library.ts

import { spawnSync } from "node:child_process";
import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { join } from "node:path";
import { type ConstantInfo, type Name, nameToString, parseExport } from "@proofscript/kernel";
import { VOCABULARY } from "../src/elab.ts";
import { ensureLean4export, LEAN_TOOLCHAIN, leanEnv } from "../src/lean.ts";
import { Hasher, meaningDeps } from "../src/library.ts";

const dir = join(homedir(), ".cache", "proofscript", "library-gen");
rmSync(dir, { recursive: true, force: true });
mkdirSync(dir, { recursive: true });
writeFileSync(join(dir, "lean-toolchain"), `${LEAN_TOOLCHAIN}\n`);
writeFileSync(join(dir, "lakefile.toml"), `name = "Vocab"\ndefaultTargets = ["Vocab"]\n\n[[lean_lib]]\nname = "Vocab"\n`);
const names = VOCABULARY.map((n) => `\`${n}`).join(", ");
writeFileSync(
  join(dir, "Vocab.lean"),
  `import Lean
open Lean

def vocabulary : List Name := [${names}]

def binderKinds : Expr → String
  | .forallE _ _ b bi => (match bi with | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c") ++ binderKinds b
  | _ => ""

#eval show CoreM Unit from do
  for n in vocabulary do
    match (← getEnv).find? n with
    | none => IO.println s!"MISSING {n}"
    | some ci => IO.println s!"BINDERS {n} {binderKinds ci.type}"
`,
);

const run = (cmd: string, args: string[]) => {
  const r = spawnSync(cmd, args, { cwd: dir, encoding: "utf8", maxBuffer: 1 << 30, env: leanEnv() });
  if (r.status !== 0) throw new Error(`${cmd} ${args.join(" ")} failed:\n${r.stdout}\n${r.stderr}`);
  return r.stdout;
};

const binders = new Map<string, string>();
const present: string[] = [];
for (const line of run("lake", ["env", "lean", "Vocab.lean"]).split("\n")) {
  const m = /^BINDERS (\S+) ?(\S*)$/.exec(line);
  if (m !== null) {
    binders.set(m[1]!, m[2]!);
    present.push(m[1]!);
  } else if (line.startsWith("MISSING ")) console.log(`not in ${LEAN_TOOLCHAIN}: ${line.slice(8)}`);
}
run("lake", ["build"]);
const text = run("lake", ["env", ensureLean4export(), "Vocab", "--", ...present]);

const env = new Map<string, ConstantInfo>();
for (const d of parseExport(text).declarations) {
  const infos: readonly ConstantInfo[] = d.kind === "inductive" ? [...d.types, ...d.ctors, ...d.recs] : d.kind === "quot" ? d.infos : [d.info];
  for (const c of infos) env.set(nameToString(c.name), c);
}

// The closure (through meaning) of the vocabulary.
const hasher = new Hasher();
const constants: Record<string, { hash: string; binders?: string }> = {};
const stack = [...present];
while (stack.length > 0) {
  const n = stack.pop()!;
  if (constants[n] !== undefined) continue;
  const c = env.get(n);
  if (c === undefined) throw new Error(`${n} missing from the export`);
  const b = binders.get(n);
  constants[n] = b === undefined ? { hash: hasher.constant(c) } : { hash: hasher.constant(c), binders: b };
  meaningDeps(c, (d: Name) => stack.push(nameToString(d)));
}

const sorted = Object.fromEntries(Object.entries(constants).sort(([a], [b]) => (a < b ? -1 : 1)));
const out = new URL("../src/library.json", import.meta.url);
writeFileSync(out, `${JSON.stringify({ toolchain: LEAN_TOOLCHAIN, constants: sorted }, null, 1)}\n`);
console.log(`${Object.keys(sorted).length} constants (${present.length} in the vocabulary) written to ${out.pathname}`);
