// `proofscript audit`: footprints collected per project, and the verified/unverified boundary.

import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { audit, auditJson, boundary } from "../src/audit.ts";
import { checkWithCertificate } from "../src/certificate.ts";
import { loadProject } from "../src/project.ts";

const mathDir = new URL("../../../examples/math/", import.meta.url).pathname;
const fixtures = new URL("./fixtures/", import.meta.url).pathname;

test("audit of examples/math (from its certificate): axioms, translations, assumptions, boundary", () => {
  const project = loadProject(join(mathDir, "tsconfig.json"));
  const a = audit(project, checkWithCertificate(project, join(mathDir, "proofscript.cert")), "certificate");
  assert.equal(a.result.theorems.filter((t) => t.status === "verified").length, a.result.theorems.length);
  assert.deepEqual(Object.keys(a.axioms).sort(), ["Classical.choice", "Quot.sound", "propext"]);
  assert.ok(a.reflected.reverse!.includes("reverse_reverse"));
  assert.ok(Object.keys(a.assumptions).every((k) => !/terminate/.test(k)), "termination is established by the certificate");
  assert.ok(a.assumptions["recursion depth below 2^30"]!.length > 0);
  // Exported functions with preconditions are the project's boundary; every internal call is checked.
  assert.deepEqual(a.boundary.map((b) => [b.kind, b.fn]), [["export", "replicate"], ["export", "zip"], ["export", "get"]]);
  assert.ok(a.trustedBase.some((t) => /elaborator/.test(t)));
  const j = JSON.parse(auditJson(a, mathDir));
  assert.equal(j.mode, "certificate");
  assert.equal(j.theorems[0].file.startsWith("src/"), true);
});

test("boundary: unverified callers of functions with preconditions are found", () => {
  const b = boundary(loadProject(join(fixtures, "boundary", "tsconfig.json")));
  assert.deepEqual(b.map((x) => [x.kind, x.fn, x.line]), [["export", "pred", 3], ["call", "pred", 14]]);
});
