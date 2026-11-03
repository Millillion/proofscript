// Runs the kernel CLI over Lean Kernel Arena tests and compares with expected outcomes.
// Usage: node scripts/arena.ts <arena-repo-dir> [glob-substring...]

import { spawnSync } from "node:child_process";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative } from "node:path";

const arena = process.argv[2];
if (arena === undefined) throw new Error("usage: arena.ts <arena-dir> [filters...]");
const filters = process.argv.slice(3);
const built = join(arena, "_build", "tests");
const cli = new URL("../src/cli.ts", import.meta.url).pathname;

function yamlField(test: string, field: string): string | undefined {
  const yaml = join(arena, "tests", `${test}.yaml`);
  if (!existsSync(yaml)) return undefined;
  return new RegExp(`^${field}:\\s*(\\S+)`, "m").exec(readFileSync(yaml, "utf8"))?.[1];
}

function expected(test: string, file: string): string {
  // `tests/<test>.yaml` holds the outcome; multi-tests put files in good/ and bad/.
  if (/\/good\//.test(file)) return "accept";
  if (/\/bad\//.test(file)) return "reject";
  const yaml = join(arena, "tests", `${test}.yaml`);
  if (!existsSync(yaml)) return "unknown";
  const m = /^outcome:\s*(\w+)/m.exec(readFileSync(yaml, "utf8"));
  return m?.[1] ?? "unknown";
}

function* walk(dir: string): Generator<string> {
  for (const f of readdirSync(dir)) {
    const p = join(dir, f);
    if (statSync(p).isDirectory()) {
      if (f !== "work") yield* walk(p);
    } else if (f.endsWith(".ndjson")) yield p;
  }
}

let pass = 0;
const failures: string[] = [];
const declined: string[] = [];
for (const file of walk(built)) {
  const rel = relative(built, file).replace(/\.ndjson$/, "");
  if (filters.length > 0 && !filters.some((f) => rel.includes(f))) continue;
  const test = rel.replace(/\/(good|bad)\/.*$/, "");
  const want = expected(test, file);
  const t0 = Date.now();
  const timeout = Number(yamlField(test, "timeout") ?? 300) * 1000;
  const r = spawnSync(process.execPath, ["--stack-size=65500", cli, file], { encoding: "utf8", timeout });
  const ms = Date.now() - t0;
  const got =
    r.status === 0 ? "accept" : r.status === 1 ? "reject" : r.status === 2 || r.signal === "SIGTERM" ? "decline" : `error(${r.status ?? r.signal})`;
  const ok = got === want || (want === "either" && (got === "accept" || got === "reject"));
  const line = `${ok ? "PASS" : got === "decline" ? "DECL" : "FAIL"} ${rel} want=${want} got=${got} ${ms}ms`;
  if (ok) pass++;
  else if (got === "decline") declined.push(`${line}\n    ${(r.stderr ?? "").trim().split("\n").pop()}`);
  else failures.push(`${line}\n    ${(r.stderr ?? "").trim().split("\n").slice(-3).join("\n    ")}`);
  console.log(line);
}
console.log(`\n${pass} passed, ${failures.length} failed, ${declined.length} declined`);
for (const f of failures) console.log(f);
for (const d of declined) console.log(d);
process.exitCode = failures.length > 0 ? 1 : 0;
