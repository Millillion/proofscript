// End-to-end tests of `proofscript check` on fixture projects. These need Lean
// (elan) and lean4export; they are skipped when Lean is not installed.

import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { type CheckResult, check } from "../src/check.ts";
import { leanAvailable } from "../src/lean.ts";

const fixtures = new URL("./fixtures/", import.meta.url).pathname;
const hasLean = leanAvailable();
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

test("good-post: postconditions are proved automatically; preconditions are enforced", { skip: !hasLean }, () => {
  const r = run("good-post");
  assert.deepEqual(r.diagnostics, []);
  assert.deepEqual(r.theorems.map((t) => t.status), ["verified", "verified"]);
  assert.ok(r.theorems[0]!.reflected.includes("append"), "the footprint names the reflected function");
});

test("bad-post: a wrong postcondition does not verify", { skip: !hasLean }, () => {
  const r = run("bad-post");
  assert.equal(r.theorems.length, 1);
  assert.equal(r.theorems[0]!.status, "failed");
});

test("good-loop: while and for loops with invariants, termination and in-bounds indexing", { skip: !hasLean }, () => {
  const r = run("good-loop");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 2);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
});

for (const name of ["bad-loop-invariant", "bad-loop-bounds", "bad-loop-termination"]) {
  test(`${name}: rejected`, { skip: !hasLean }, () => {
    const r = run(name);
    assert.ok(r.diagnostics.length > 0, "a diagnostic is reported");
    assert.ok(r.theorems.every((t) => t.status !== "verified"), "nothing is reported as verified");
  });
}

test("good-overflow: bounded arithmetic and counting verify; counting is listed as an assumption", { skip: !hasLean }, () => {
  const r = run("good-overflow");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 3 && r.theorems.every((t) => t.status === "verified"));
  const len = r.theorems.find((t) => t.tsName.startsWith("length"))!;
  assert.ok(len.assumptions.some((a) => /recursion depth/.test(a)));
});

test("bad-overflow: unbounded multiplication is rejected", { skip: !hasLean }, () => {
  const r = run("bad-overflow");
  assert.ok(r.diagnostics.length > 0);
  assert.ok(r.theorems.every((t) => t.status !== "verified"));
});

test("good-struct: plain object types and interfaces are structures", { skip: !hasLean }, () => {
  const r = run("good-struct");
  assert.deepEqual(r.diagnostics, []);
  assert.deepEqual(r.theorems.map((t) => t.status), ["verified", "verified"]);
});

test("good-string: strings are UTF-16 code units, as in JavaScript", { skip: !hasLean }, () => {
  const r = run("good-string");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length === 3 && r.theorems.every((t) => t.status === "verified"));
});

for (const name of ["bad-string", "bad-struct"]) {
  test(`${name}: rejected`, { skip: !hasLean }, () => {
    const r = run(name);
    assert.ok(r.diagnostics.length > 0);
    assert.ok(r.theorems.every((t) => t.status !== "verified"));
  });
}

test("mixed: a failing theorem does not prevent checking the others", { skip: !hasLean }, () => {
  const r = run("mixed");
  const by = new Map(r.theorems.map((t) => [t.tsName, t.status]));
  assert.equal(by.get("good"), "verified");
  assert.equal(by.get("bad"), "failed");
});

test("good-mutation: in-place writes, push, mutable fields, Old, modifying calls", { skip: !hasLean }, () => {
  const r = run("good-mutation");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 4 && r.theorems.every((t) => t.status === "verified"));
  const swap = r.theorems.find((t) => t.tsName.startsWith("swapAt"))!;
  assert.ok(swap.assumptions.includes("callers do not alias modified arguments"));
});

for (const name of ["bad-alias", "bad-undeclared-modify", "bad-old", "bad-write-oob"]) {
  test(`${name}: rejected`, { skip: !hasLean }, () => {
    const r = run(name);
    assert.ok(r.diagnostics.length > 0, "a diagnostic is reported");
    assert.ok(r.theorems.every((t) => t.status !== "verified"));
  });
}

test("good-indexed: value-indexed types (Vec, Fin, typeof n), value parameters, modular postconditions", { skip: !hasLean }, () => {
  const r = run("good-indexed");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 6 && r.theorems.every((t) => t.status === "verified"));
});

test("bad-indexed: an out-of-range Fin index is rejected", { skip: !hasLean }, () => {
  const r = run("bad-indexed");
  assert.ok(r.diagnostics.some((d) => /precondition/.test(d.message)));
  assert.ok(r.theorems.every((t) => t.status !== "verified"));
});

test("examples/math: the whole library verifies", { skip: !hasLean }, () => {
  const r = check(new URL("../../../examples/math/tsconfig.json", import.meta.url).pathname);
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.theorems.length >= 28, `expected the library's theorems, got ${r.theorems.length}`);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
});

test("bad-caller: a function without a spec that calls one with preconditions is checked", { skip: !hasLean }, () => {
  const r = run("bad-caller");
  assert.ok(r.diagnostics.some((d) => /precondition may not hold at a call in bad/.test(d.message)));
});

test("boundary: callers outside the logic are reported, never silently trusted", { skip: !hasLean }, () => {
  const r = run("boundary");
  assert.deepEqual(r.diagnostics, []);
  assert.ok(r.unverified.some((u) => /call of pred from a function outside the logic/.test(u.message)));
});

test("examples/tutorial: every step of the tutorial verifies", { skip: !hasLean }, () => {
  const r = check(new URL("../../../examples/tutorial/tsconfig.json", import.meta.url).pathname);
  assert.deepEqual(r.diagnostics, []);
  assert.equal(r.theorems.length, 12);
  assert.ok(r.theorems.every((t) => t.status === "verified"));
});
