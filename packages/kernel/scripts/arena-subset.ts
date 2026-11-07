// Packs a light subset of the Lean Kernel Arena (bugs, corner cases, other, tutorial,
// Init.Prelude) into test/arena/, so that CI checks the kernel against it without Lean.
// Usage: node --stack-size=65500 scripts/arena-subset.ts <arena-repo-dir>
//
// Tests that take more than a few seconds here, and those whose outcome is unknown, are left
// out: the full arena run (scripts/arena.ts) covers them.

import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { gzipSync } from "node:zlib";

const arena = process.argv[2];
if (arena === undefined) throw new Error("usage: arena-subset.ts <arena-dir>");
const built = join(arena, "_build", "tests");
const out = new URL("../test/arena/", import.meta.url).pathname;
const cli = new URL("../src/cli.ts", import.meta.url).pathname;
const LIMIT_MS = 5000;

function expected(test: string, file: string): string {
  if (/\/good\//.test(file)) return "accept";
  if (/\/bad\//.test(file)) return "reject";
  const yaml = join(arena, "tests", `${test}.yaml`);
  if (!existsSync(yaml)) return "unknown";
  return /^outcome:\s*(\w+)/m.exec(readFileSync(yaml, "utf8"))?.[1] ?? "unknown";
}

function* walk(dir: string): Generator<string> {
  for (const f of readdirSync(dir)) {
    const p = join(dir, f);
    if (statSync(p).isDirectory()) yield* walk(p);
    else if (f.endsWith(".ndjson")) yield p;
  }
}

rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });
const files = [...["bugs", "corner-cases", "other", "tutorial"].flatMap((d) => [...walk(join(built, d))]), join(built, "init-prelude.ndjson")];
const manifest: { file: string; test: string; expected: string }[] = [];
let skipped = 0;
for (const f of files) {
  const rel = relative(built, f);
  const test = rel.replace(/\.ndjson$/, "").replace(/\/(good|bad)\/[^/]*$/, "");
  const exp = expected(test, f);
  if (exp !== "accept" && exp !== "reject") {
    skipped++;
    continue;
  }
  const t0 = Date.now();
  const r = spawnSync(process.execPath, ["--stack-size=65500", "--max-old-space-size=2048", cli, f], { encoding: "utf8", timeout: LIMIT_MS });
  const ms = Date.now() - t0;
  const got = r.status === 0 ? "accept" : r.status === 1 ? "reject" : "decline";
  if (ms >= LIMIT_MS || got === "decline") {
    skipped++;
    continue;
  }
  if (got !== exp) throw new Error(`${rel}: expected ${exp}, got ${got} (fix the kernel before packing)`);
  const name = `${rel.replace(/[\\/]/g, "__")}.gz`;
  writeFileSync(join(out, name), gzipSync(readFileSync(f), { level: 9 }));
  manifest.push({ file: name, test, expected: exp });
}
writeFileSync(join(out, "manifest.json"), `${JSON.stringify(manifest, null, 1)}\n`);
writeFileSync(
  join(out, "NOTICE"),
  "These exports are from the Lean Kernel Arena (https://github.com/leanprover/lean-kernel-arena),\n" +
    "licensed under the Apache License 2.0, and are used here unmodified (gzipped).\n",
);
console.log(`${manifest.length} tests packed (${manifest.filter((m) => m.expected === "reject").length} must be rejected), ${skipped} left out`);
