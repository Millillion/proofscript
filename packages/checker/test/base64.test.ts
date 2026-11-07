// examples/base64: a verified drop-in replacement for base64-js, against base64-js's own tests.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { join } from "node:path";
import { test } from "node:test";
import { checkWithCertificate } from "../src/certificate.ts";
import { check } from "../src/check.ts";
import { leanAvailable } from "../src/lean.ts";
import { loadProject } from "../src/project.ts";

const dir = new URL("../../../examples/base64/", import.meta.url).pathname;
const node = (args: string[]) => spawnSync(process.execPath, ["--max-old-space-size=2048", ...args], { cwd: dir, encoding: "utf8" });

test("examples/base64 verifies with Lean", { skip: !leanAvailable() }, () => {
  const r = check(join(dir, "tsconfig.json"));
  assert.deepEqual(r.diagnostics, []);
  assert.equal(r.theorems.length, 19);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
  // The wrapper's calls are the boundary: reported, not proved.
  assert.equal(r.unverified.length, 2);
});

test("examples/base64 verifies from its committed certificate, without Lean", () => {
  const r = checkWithCertificate(loadProject(join(dir, "tsconfig.json")), join(dir, "proofscript.cert"));
  assert.deepEqual(r.diagnostics, []);
  assert.equal(r.theorems.length, 19);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
});

test("examples/base64 passes base64-js's own test suite (including 64 MB of data)", () => {
  const tape = new URL("../../../node_modules/tape/bin/tape", import.meta.url).pathname;
  const r = node([tape, "test/convert.cjs", "test/url-safe.cjs", "test/big-data.cjs", "test/corrupt.cjs"]);
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.match(r.stdout, /# pass {2}57/);
});

test("examples/base64 agrees with base64-js on random inputs", () => {
  const r = node(["--test", "test/differential.mjs"]);
  assert.equal(r.status, 0, r.stdout + r.stderr);
});
