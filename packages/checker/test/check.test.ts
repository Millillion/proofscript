// End-to-end tests of `proofscript check` on fixture projects. These need Lean
// (elan) and lean4export; they are skipped when Lean is not installed.

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { join } from "node:path";
import { test } from "node:test";
import { type CheckResult, check } from "../src/check.ts";

const fixtures = new URL("./fixtures/", import.meta.url).pathname;
const hasLean = spawnSync("lake", ["--version"]).status === 0;
const run = (name: string): CheckResult => check(join(fixtures, name, "tsconfig.json"));

test("good-nat: arithmetic theorems verify, with no axioms beyond the standard ones", { skip: !hasLean }, () => {
  const r = run("good-nat");
  assert.deepEqual(r.diagnostics, []);
  assert.deepEqual(r.theorems.map((t) => [t.tsName, t.status]), [
    ["add_comm", "verified"],
    ["double_ge", "verified"],
  ]);
  assert.ok(r.declarationsChecked > 0);
});

test("good-list: a theorem about a recursive data type verifies", { skip: !hasLean }, () => {
  const r = run("good-list");
  assert.deepEqual(r.diagnostics, []);
  assert.deepEqual(r.theorems.map((t) => [t.tsName, t.status]), [["size_mirror", "verified"]]);
});

test("bad-false: a false theorem does not verify", { skip: !hasLean }, () => {
  const r = run("bad-false");
  assert.equal(r.theorems.length, 1);
  assert.equal(r.theorems[0]!.status, "failed");
  assert.ok(r.diagnostics.some((d) => /proof failed/.test(d.message)));
});

test("bad-sorry: a proof with `sorry` is admitted, not verified", { skip: !hasLean }, () => {
  const r = run("bad-sorry");
  assert.equal(r.theorems[0]!.status, "admitted");
  assert.ok(r.theorems[0]!.axioms.includes("sorry"));
});

test("bad-number: floating-point arithmetic is not treated as integer arithmetic", () => {
  const r = run("bad-number");
  assert.equal(r.theorems.length, 0);
  assert.ok(r.diagnostics.some((d) => /IEEE-754/.test(d.message)));
});

test("bad-identity: `===` on objects is not structural equality", () => {
  const r = run("bad-identity");
  assert.equal(r.theorems.length, 0);
  assert.ok(r.diagnostics.some((d) => /compares identity/.test(d.message)));
});
