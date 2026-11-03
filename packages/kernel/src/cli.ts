// `proofscript-kernel <file.ndjson>`: checks a lean4export file.
// Exit codes follow the Lean Kernel Arena: 0 accept, 1 reject, 2 decline.

import { readFileSync } from "node:fs";
import { Kernel } from "./check.ts";
import { KernelError } from "./env.ts";
import { exprAny } from "./expr.ts";
import { name, nameToString } from "./name.ts";
import { parseExport } from "./ndjson.ts";

/** Constants whose meaning depends on running compiled code, which this kernel does not do. */
const NATIVE = new Set([name("Lean.reduceBool"), name("Lean.reduceNat")]);

class Decline extends Error {}

function main(): number {
  const path = process.argv[2];
  const text = readFileSync(path === undefined || path === "-" ? 0 : path, "utf8");
  const verbose = process.argv.includes("-v");
  let decls;
  try {
    decls = parseExport(text).declarations;
  } catch (e) {
    if (e instanceof KernelError) {
      console.error(`rejected: malformed export: ${e.message}`);
      return 1;
    }
    throw e;
  }
  const kernel = new Kernel();
  let current = "";
  try {
    for (const d of decls) {
      const info = d.kind === "quot" ? d.infos[0] : d.kind === "inductive" ? d.types[0] : d.info;
      current = info === undefined ? "?" : nameToString(info.name);
      if (verbose) console.error(current);
      if (d.kind !== "quot" && d.kind !== "inductive" && "value" in d.info) {
        if (exprAny(d.info.value, (e) => e.kind === "const" && NATIVE.has(e.name))) throw new Decline(current);
      }
      kernel.add(d);
    }
    kernel.finish();
  } catch (e) {
    if (e instanceof Decline) {
      console.error(`declined: ${e.message} relies on native code evaluation`);
      return 2;
    }
    if (e instanceof KernelError) {
      console.error(`rejected: ${current}: ${e.message}`);
      return 1;
    }
    if (e instanceof RangeError) {
      console.error(`declined: ${current}: ${e.message}`);
      return 2;
    }
    throw e;
  }
  console.error(`accepted: ${decls.length} declarations`);
  return 0;
}

process.exitCode = main();
