// `proofscript check [--write-certificate [file]] [--certificate [file]] [tsconfig.json | files…]`

import { existsSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { checkWithCertificate } from "./certificate.ts";
import { type CheckResult, check, formatResult } from "./check.ts";
import { leanAvailable } from "./lean.ts";
import { loadProject } from "./project.ts";

const USAGE = `usage: proofscript check [options] [tsconfig.json | files…]

  --write-certificate [file]  prove with Lean and save a certificate (default: proofscript.cert)
  --certificate [file]        check against a certificate, without Lean (default: proofscript.cert)`;

function main(): number {
  const [cmd, ...rest] = process.argv.slice(2);
  if (cmd !== "check") {
    console.error(USAGE);
    return 2;
  }
  let write: string | true | undefined;
  let replay: string | true | undefined;
  const targets: string[] = [];
  for (let i = 0; i < rest.length; i++) {
    const a = rest[i]!;
    if (a === "--write-certificate" || a === "--certificate") {
      const next = rest[i + 1];
      const file = next !== undefined && next.endsWith(".cert") ? (i++, next) : true;
      if (a === "--certificate") replay = file;
      else write = file;
    } else if (a.startsWith("-")) {
      console.error(`unknown option ${a}\n${USAGE}`);
      return 2;
    } else targets.push(a);
  }
  if (write !== undefined && replay !== undefined) {
    console.error("use either --write-certificate or --certificate");
    return 2;
  }
  const target = targets.length === 0 ? "tsconfig.json" : targets.length === 1 && targets[0]!.endsWith(".json") ? targets[0]! : targets;
  if (typeof target === "string" && !existsSync(target)) {
    console.error(`no ${target} found; pass a tsconfig.json or source files`);
    return 2;
  }
  const root = typeof target === "string" ? dirname(resolve(target)) : dirname(resolve(target[0]!));
  const certPath = (f: string | true) => (f === true ? join(root, "proofscript.cert") : resolve(f));

  let result: CheckResult;
  if (replay !== undefined) {
    const path = certPath(replay);
    if (!existsSync(path)) {
      console.error(`no certificate at ${path}; make one with \`proofscript check --write-certificate\``);
      return 2;
    }
    result = checkWithCertificate(loadProject(target), path);
  } else {
    if (!leanAvailable()) {
      console.error(
        "Proving needs Lean. Install elan (https://lean-lang.org/install); ProofScript then installs its pinned Lean version itself.\n" +
          "Without Lean, a project with a certificate can be checked with `proofscript check --certificate`.",
      );
      return 2;
    }
    result = check(target, write === undefined ? {} : { writeCertificate: certPath(write) });
  }
  console.log(formatResult(result, root));
  if (write !== undefined) console.log(`certificate written to ${certPath(write)}`);
  const ok = result.diagnostics.length === 0 && result.theorems.every((t) => t.status === "verified");
  return ok ? 0 : 1;
}

process.exitCode = main();
