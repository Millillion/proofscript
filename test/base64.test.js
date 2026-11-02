import assert from "node:assert/strict";
import crypto from "node:crypto";
import { readFileSync } from "node:fs";
import test from "node:test";
import { createRequire } from "node:module";
import path from "node:path";
import { pathToFileURL } from "node:url";

import { verifyProofScriptModule } from "../dist/verify.js";

const require = createRequire(import.meta.url);
const upstreamModule = require("./fixtures/base64-js-upstream.cjs");
const examplePath = path.resolve("examples/base64-js.proof.ts");
const verification = await verifyProofScriptModule(examplePath);
const exampleModule = await import(`${pathToFileURL(verification.emittedJavaScriptPath).href}?test=${Date.now()}`);

test("ProofScript emits a proof artifact for the upstream-style base64 module", () => {
  const sourceText = readFileSync(examplePath, "utf8");
  assert.equal(verification.proofArtifact.theorems.length, 18);
  assert.ok(verification.proofArtifactPath.endsWith("base64-js.proof.json"));
  assert.ok(sourceText.includes("ProofScriptSpec<typeof sextetAtSpec>"));
  assert.ok(sourceText.includes("ProofScriptImpl<typeof toByteArray, typeof toByteArraySpec>"));
  assert.ok(!sourceText.includes("@spec"));
  assert.ok(!sourceText.includes("@ensures"));
  const theoremByName = new Map(verification.proofArtifact.theorems.map((theorem) => [theorem.name, theorem]));
  assert.equal(theoremByName.get("sextetAtMatchesSpec")?.checkedCases, 64);
  assert.equal(theoremByName.get("encodeChunkMatchesSpec")?.kind, "loopJoin");
  assert.equal(theoremByName.get("fromByteArrayMatchesSpec")?.kind, "loopJoinTail");
  assert.equal(theoremByName.get("toByteArrayMatchesSpec")?.kind, "loopWrite");
  assert.equal(theoremByName.get("firstPaddingIndexFromMatchesSpec")?.kind, "recursiveAdvance");
  assert.equal(theoremByName.get("firstPaddingIndexMatchesSpec")?.kind, "composition");
  assert.equal(theoremByName.get("getLensMatchesSpec")?.kind, "composition");
  assert.equal(theoremByName.get("charToSextetMatchesSpec")?.checkedCases, 65536);
});

test("convert strings to base64 and back", () => {
  const checks = ["a", "aa", "aaa", "hi", "hi!", "hi!!", "sup", "sup?", "sup?!"];

  for (const check of checks) {
    const bytes = Array.from(Buffer.from(check, "utf8"));
    const b64 = exampleModule.fromByteArray(bytes);
    const roundTrip = Buffer.from(exampleModule.toByteArray(b64)).toString("utf8");
    assert.equal(roundTrip, check);
    assert.equal(exampleModule.byteLength(b64), bytes.length);
  }
});

test("matches known upstream conversion examples including signed byte inputs", () => {
  const data = [
    [[0, 0, 0], "AAAA"],
    [[0, 0, 1], "AAAB"],
    [[0, 1, -1], "AAH/"],
    [[1, 1, 1], "AQEB"],
    [[0, -73, 23], "ALcX"],
  ];

  for (const [bytes, expected] of data) {
    assert.equal(exampleModule.fromByteArray(bytes), expected);
    assert.deepEqual(Array.from(exampleModule.toByteArray(expected)), bytes.map((value) => value & 0xff));
    assert.equal(exampleModule.byteLength(expected), bytes.length);
  }
});

test("supports URL-safe decoding and corrupt padding behavior from upstream tests", () => {
  const expected = [0xff, 0xff, 0xbe, 0xff, 0xef, 0xbf, 0xfb, 0xef, 0xff];

  assert.deepEqual(Array.from(exampleModule.toByteArray("//++/++/++//")), expected);
  assert.equal(exampleModule.byteLength("//++/++/++//"), expected.length);

  assert.deepEqual(Array.from(exampleModule.toByteArray("__--_--_--__")), expected);
  assert.equal(exampleModule.byteLength("__--_--_--__"), expected.length);

  assert.deepEqual(Array.from(exampleModule.toByteArray("SQ==QU0=")), [73]);
  assert.equal(exampleModule.byteLength("SQ==QU0="), 1);
});

test("rejects invalid lengths", () => {
  assert.throws(
    () => exampleModule.byteLength("abc"),
    /Invalid string\. Length must be a multiple of 4/,
  );
  assert.throws(
    () => exampleModule.toByteArray("abc"),
    /Invalid string\. Length must be a multiple of 4/,
  );
});

test("matches the upstream repository implementation on randomized cases", () => {
  for (let index = 0; index < 40; index += 1) {
    const length = index * 7;
    const bytes = Array.from(crypto.randomBytes(length));
    const maybeSigned = bytes.map((value, position) => (position % 5 === 0 ? value - 256 : value));
    const expectedBase64 = upstreamModule.fromByteArray(maybeSigned);
    const actualBase64 = exampleModule.fromByteArray(maybeSigned);
    assert.equal(actualBase64, expectedBase64);

    const decodedActual = Array.from(exampleModule.toByteArray(expectedBase64));
    const decodedExpected = Array.from(upstreamModule.toByteArray(expectedBase64));
    assert.deepEqual(decodedActual, decodedExpected);
    assert.equal(exampleModule.byteLength(expectedBase64), upstreamModule.byteLength(expectedBase64));
  }
});
