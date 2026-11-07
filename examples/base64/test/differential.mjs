// Differential test: this implementation and base64-js 1.5.1 on random inputs, including
// URL-safe characters, invalid characters and unusual padding. Outputs must be identical,
// or both must throw.
import assert from "node:assert/strict";
import { test } from "node:test";
import * as ours from "../src/index.ts";
import * as reference from "base64-js";

let seed = 0x9e3779b9;
const rand = (n) => {
  seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) + 0x6d2b79f5) | 0;
  return ((seed >>> 0) % n);
};
const alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/-_=*. é";

function same(f, x) {
  let a, b, ea, eb;
  try { a = f(ours, x); } catch (e) { ea = e; }
  try { b = f(reference, x); } catch (e) { eb = e; }
  if (ea !== undefined || eb !== undefined) {
    assert.ok(ea !== undefined && eb !== undefined, `only one throws on ${JSON.stringify(x)}: ${ea ?? eb}`);
    assert.equal(ea.constructor, eb.constructor);
    return;
  }
  assert.deepEqual(a, b, `differs on ${JSON.stringify(x)}`);
}

test("fromByteArray agrees on random bytes (Uint8Array and arrays)", () => {
  for (let t = 0; t < 3000; t++) {
    const n = rand(40);
    const u = new Uint8Array(n);
    for (let i = 0; i < n; i++) u[i] = rand(256);
    same((m, x) => m.fromByteArray(x), u);
    same((m, x) => m.fromByteArray(x), Array.from(u));
  }
});

test("fromByteArray agrees on integers outside 0..255 in whole groups (masked, as base64-js)", () => {
  for (let t = 0; t < 2000; t++) {
    const n = 3 * rand(10);
    const a = Array.from({ length: n }, () => rand(2000) - 1000);
    same((m, x) => m.fromByteArray(x), a);
  }
});

test("toByteArray and byteLength agree on random strings", () => {
  for (let t = 0; t < 20000; t++) {
    const n = rand(5) === 0 ? rand(10) : 4 * rand(10);
    let s = "";
    for (let i = 0; i < n; i++) s += alphabet[rand(rand(4) === 0 ? alphabet.length : 64)];
    same((m, x) => m.toByteArray(x), s);
    same((m, x) => m.byteLength(x), s);
  }
});

test("round trip on random bytes", () => {
  for (let t = 0; t < 2000; t++) {
    const u = Uint8Array.from({ length: rand(100) }, () => rand(256));
    assert.deepEqual(ours.toByteArray(ours.fromByteArray(u)), u);
  }
});
