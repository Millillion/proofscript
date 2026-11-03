// `proofscript check [tsconfig.json | files…]`

import { existsSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { check, formatResult } from "./check.ts";

function main(): number {
  const [cmd, ...rest] = process.argv.slice(2);
  if (cmd !== "check") {
    console.error("usage: proofscript check [tsconfig.json | files…]");
    return 2;
  }
  const target = rest.length === 0 ? "tsconfig.json" : rest.length === 1 && rest[0]!.endsWith(".json") ? rest[0]! : rest;
  if (typeof target === "string" && !existsSync(target)) {
    console.error(`no ${target} found; pass a tsconfig.json or source files`);
    return 2;
  }
  const result = check(target);
  const root = typeof target === "string" ? dirname(resolve(target)) : dirname(resolve(target[0]!));
  console.log(formatResult(result, root));
  const ok = result.diagnostics.length === 0 && result.theorems.every((t) => t.status === "verified");
  return ok ? 0 : 1;
}

process.exitCode = main();
