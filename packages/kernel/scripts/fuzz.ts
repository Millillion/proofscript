// Differential mutation fuzzing against Lean's official kernel.
//
// Takes accepted export files, applies one random mutation to each (perturb a
// de Bruijn index, retarget a constant/level/expression reference, change a
// universe level, alter declaration metadata), and runs both this kernel and
// the official one. Any accept/reject disagreement is reported and saved.
//
// Usage: node scripts/fuzz.ts <official-kernel-binary> <iterations> <file.ndjson>...

import { spawnSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { basename, join } from "node:path";
import { tmpdir } from "node:os";

const [official, itersArg, ...files] = process.argv.slice(2);
if (official === undefined || itersArg === undefined || files.length === 0) {
  throw new Error("usage: fuzz.ts <official-kernel> <iterations> <file.ndjson>...");
}
const iterations = Number(itersArg);
const cli = new URL("../src/cli.ts", import.meta.url).pathname;
const outDir = join(tmpdir(), "proofscript-fuzz");
mkdirSync(outDir, { recursive: true });

let seed = Number(process.env.SEED ?? Date.now()) >>> 0;
function rand(n: number): number {
  seed ^= seed << 13;
  seed ^= seed >>> 17;
  seed ^= seed << 5;
  return (seed >>> 0) % n;
}

type Json = { [k: string]: any };

/** One random mutation of one line; returns undefined if this line offers nothing to mutate. */
function mutate(lines: Json[], i: number, counts: { names: number; levels: number; exprs: number }): Json | undefined {
  const o = structuredClone(lines[i]!);
  const pickExpr = (max: number) => rand(Math.max(1, max));
  if ("bvar" in o) o.bvar = Math.max(0, o.bvar + (rand(2) === 0 ? 1 : -1));
  else if ("sort" in o) o.sort = rand(Math.max(1, counts.levels));
  else if ("const" in o) {
    if (rand(2) === 0 && o.const.us.length > 0) o.const.us[rand(o.const.us.length)] = rand(Math.max(1, counts.levels));
    else o.const.name = rand(Math.max(1, counts.names));
  } else if ("app" in o) {
    if (rand(2) === 0) o.app.fn = pickExpr(o.ie);
    else o.app.arg = pickExpr(o.ie);
  } else if ("lam" in o || "forallE" in o) {
    const b = o.lam ?? o.forallE;
    if (rand(2) === 0) b.type = pickExpr(o.ie);
    else b.body = pickExpr(o.ie);
  } else if ("proj" in o) {
    if (rand(2) === 0) o.proj.idx = o.proj.idx + 1;
    else o.proj.struct = pickExpr(o.ie);
  } else if ("succ" in o) o.succ = rand(Math.max(1, o.il));
  else if ("max" in o || "imax" in o) {
    const k = "max" in o ? "max" : "imax";
    o[k][rand(2)] = rand(Math.max(1, o.il));
  } else if ("natVal" in o) o.natVal = String(BigInt(o.natVal) + 1n);
  else if ("thm" in o || "def" in o || "axiom" in o || "opaque" in o) {
    const d = o.thm ?? o.def ?? o.axiom ?? o.opaque;
    if ("value" in d && rand(2) === 0) d.value = rand(Math.max(1, counts.exprs));
    else d.type = rand(Math.max(1, counts.exprs));
  } else if ("inductive" in o) {
    const d = o.inductive;
    const which = rand(4);
    if (which === 0 && d.recs.length > 0) {
      const r = d.recs[rand(d.recs.length)];
      if (r.rules.length > 0) r.rules[rand(r.rules.length)].rhs = rand(Math.max(1, counts.exprs));
      else r.k = !r.k;
    } else if (which === 1 && d.ctors.length > 0) {
      d.ctors[rand(d.ctors.length)].type = rand(Math.max(1, counts.exprs));
    } else if (which === 2) {
      const t = d.types[rand(d.types.length)];
      t.numParams = Math.max(0, t.numParams + (rand(2) === 0 ? 1 : -1));
    } else if (d.recs.length > 0) {
      d.recs[rand(d.recs.length)].k = !d.recs[0].k;
    } else return undefined;
  } else return undefined;
  return o;
}

function run(cmd: string, args: string[]): "accept" | "reject" | "other" {
  const r = spawnSync(cmd, args, { encoding: "utf8", timeout: 60_000 });
  return r.status === 0 ? "accept" : r.status === 1 ? "reject" : "other";
}

let agree = 0;
let skipped = 0;
const disagreements: string[] = [];
for (let it = 0; it < iterations; it++) {
  const file = files[rand(files.length)]!;
  const lines = readFileSync(file, "utf8").split("\n").filter((l) => l.trim() !== "").map((l) => JSON.parse(l) as Json);
  const counts = { names: 0, levels: 0, exprs: 0 };
  for (const o of lines) {
    if ("in" in o) counts.names = Math.max(counts.names, o.in + 1);
    if ("il" in o) counts.levels = Math.max(counts.levels, o.il + 1);
    if ("ie" in o) counts.exprs = Math.max(counts.exprs, o.ie + 1);
  }
  let mutated: Json | undefined;
  let idx = 0;
  for (let tries = 0; tries < 50 && mutated === undefined; tries++) {
    idx = 1 + rand(lines.length - 1);
    mutated = mutate(lines, idx, counts);
  }
  if (mutated === undefined) {
    skipped++;
    continue;
  }
  const copy = lines.slice();
  copy[idx] = mutated;
  const path = join(outDir, `mut-${it}.ndjson`);
  writeFileSync(path, copy.map((o) => JSON.stringify(o)).join("\n") + "\n");
  const ours = run(process.execPath, ["--stack-size=65500", cli, path]);
  const theirs = run(official, [path]);
  if (ours === "other" || theirs === "other") {
    skipped++;
  } else if (ours === theirs) {
    agree++;
  } else {
    const keep = join(outDir, `disagree-${basename(file, ".ndjson")}-${it}.ndjson`);
    writeFileSync(keep, readFileSync(path));
    disagreements.push(`${keep}: ours=${ours} official=${theirs} (line ${idx + 1})`);
    console.log(`DISAGREE ${keep}: ours=${ours} official=${theirs}`);
  }
}
console.log(`\n${agree} agree, ${disagreements.length} disagree, ${skipped} skipped`);
for (const d of disagreements) console.log(d);
process.exitCode = disagreements.length > 0 ? 1 : 0;
