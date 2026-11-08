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
  assert.equal(r.theorems.length, 32);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
  // The wrapper's calls are the boundary: reported, not proved.
  assert.equal(r.unverified.length, 2);
});

test("examples/base64 verifies from its committed certificate, without Lean", () => {
  const r = checkWithCertificate(loadProject(join(dir, "tsconfig.json")), join(dir, "proofscript.cert"));
  // Known gap (0.0.11): Lean cannot elaborate the equations of the two tail functions (a
  // chain of `Array.set` on a parameter), so the certificate reports them, and the two
  // entry points that call them, as not covered.
  assert.deepEqual(
    r.diagnostics.map((d) => d.message.replace(/ \(.*/, "")),
    [
      "definition encodeTail is not covered by the certificate",
      "definition encodeInto is not covered by the certificate",
      "definition decodeTail is not covered by the certificate",
      "definition decodeInto is not covered by the certificate",
    ],
  );
  assert.equal(r.theorems.length, 32);
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
