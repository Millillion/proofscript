// `proofscript-kernel <file.ndjson>`: checks a lean4export file.
// Exit codes follow the Lean Kernel Arena: 0 accept, 1 reject, 2 decline.
// The file is streamed, so exports larger than V8's maximum string length work.

import { closeSync, openSync, readSync } from "node:fs";
import { StringDecoder } from "node:string_decoder";
import { Kernel } from "./check.ts";
import { type Declaration, KernelError } from "./env.ts";
import { exprAny } from "./expr.ts";
import { name, nameToString } from "./name.ts";
import { ExportReader } from "./ndjson.ts";

/** Constants whose meaning depends on running compiled code, which this kernel does not do. */
const NATIVE = new Set([name("Lean.reduceBool"), name("Lean.reduceNat")]);

class Decline extends Error {}

function* lines(path: string | undefined): Generator<string> {
  const fd = path === undefined || path === "-" ? 0 : openSync(path, "r");
  const buf = Buffer.alloc(1 << 22);
  const decoder = new StringDecoder("utf8");
  let rest = "";
  for (;;) {
    const n = readSync(fd, buf, 0, buf.length, null);
    if (n === 0) break;
    const chunk = rest + decoder.write(buf.subarray(0, n));
    const parts = chunk.split("\n");
    rest = parts.pop()!;
    yield* parts;
  }
  rest += decoder.end();
  if (rest !== "") yield rest;
  if (fd !== 0) closeSync(fd);
}

function main(): number {
  const args = process.argv.slice(2);
  const verbose = args.includes("-v");
  const path = args.find((a) => !a.startsWith("-"));
  const reader = new ExportReader();
  const kernel = new Kernel();
  let current = "";
  let count = 0;
  const check = (d: Declaration): void => {
    const info = d.kind === "quot" ? d.infos[0] : d.kind === "inductive" ? d.types[0] : d.info;
    current = info === undefined ? "?" : nameToString(info.name);
    if (verbose) console.error(current);
    if (d.kind !== "quot" && d.kind !== "inductive" && "value" in d.info) {
      if (exprAny(d.info.value, (e) => e.kind === "const" && NATIVE.has(e.name))) throw new Decline(current);
    }
    kernel.add(d);
    count++;
  };
  try {
    for (const line of lines(path)) for (const d of reader.line(line)) check(d);
    for (const d of reader.end()) check(d);
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
  console.error(`accepted: ${count} declarations`);
  return 0;
}

process.exitCode = main();
