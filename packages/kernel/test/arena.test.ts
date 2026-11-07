// A light subset of the Lean Kernel Arena (scripts/arena-subset.ts): every recorded kernel
// soundness bug, the corner cases and the tutorial must be judged as the arena expects.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { gunzipSync } from "node:zlib";
import { Kernel, KernelError, parseExport } from "../src/index.ts";

const dir = new URL("./arena/", import.meta.url);
const manifest = JSON.parse(readFileSync(new URL("manifest.json", dir), "utf8")) as { file: string; test: string; expected: "accept" | "reject" }[];

function judge(text: string): "accept" | "reject" {
  try {
    const k = new Kernel();
    for (const d of parseExport(text).declarations) k.add(d);
    k.finish();
    return "accept";
  } catch (e) {
    if (e instanceof KernelError) return "reject";
    throw e;
  }
}

for (const group of ["bugs", "corner-cases", "other", "tutorial", "init-prelude"]) {
  const cases = manifest.filter((m) => m.test === group || m.test.startsWith(`${group}/`));
  test(`Lean Kernel Arena: ${group} (${cases.length} tests)`, () => {
    const wrong: string[] = [];
    for (const c of cases) {
      const got = judge(gunzipSync(readFileSync(new URL(c.file, dir))).toString("utf8"));
      if (got !== c.expected) wrong.push(`${c.file}: expected ${c.expected}, got ${got}`);
    }
    assert.deepEqual(wrong, []);
  });
}
