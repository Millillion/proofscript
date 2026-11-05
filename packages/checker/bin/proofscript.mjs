#!/usr/bin/env node
// The `proofscript` command: runs the checker with the stack it needs (deep proof terms).
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const cli = fileURLToPath(new URL("../src/cli.ts", import.meta.url));
const r = spawnSync(process.execPath, ["--stack-size=65500", "--max-old-space-size=4096", cli, ...process.argv.slice(2)], { stdio: "inherit" });
process.exitCode = r.status ?? 1;
