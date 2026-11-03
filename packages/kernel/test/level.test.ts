import assert from "node:assert/strict";
import { test } from "node:test";
import { type Level, geq, imax, instantiateLevel, levelEquiv, max, ofNat, param, succ, zero } from "../src/level.ts";
import { name } from "../src/name.ts";

const u = param(name("u"));
const v = param(name("v"));
const w = param(name("w"));

/** Evaluates a level under an assignment of naturals to parameters. */
function evalLevel(l: Level, env: Map<string, number>): number {
  switch (l.kind) {
    case "zero":
      return 0;
    case "param":
      return env.get((l.name as { str: string }).str) ?? 0;
    case "succ":
      return evalLevel(l.of, env) + 1;
    case "max":
      return Math.max(evalLevel(l.lhs, env), evalLevel(l.rhs, env));
    case "imax": {
      const b = evalLevel(l.rhs, env);
      return b === 0 ? 0 : Math.max(evalLevel(l.lhs, env), b);
    }
  }
}

/** Brute-force `l1 >= l2` over assignments in 0..3 (sufficient for levels with offsets < 3). */
function bruteGeq(l1: Level, l2: Level): boolean {
  for (let a = 0; a <= 3; a++)
    for (let b = 0; b <= 3; b++)
      for (let c = 0; c <= 3; c++) {
        const env = new Map([
          ["u", a],
          ["v", b],
          ["w", c],
        ]);
        if (evalLevel(l1, env) < evalLevel(l2, env)) return false;
      }
  return true;
}

test("basic facts", () => {
  assert.ok(geq(succ(u), u));
  assert.ok(!geq(u, succ(u)));
  assert.ok(geq(max(u, v), u));
  assert.ok(!geq(u, max(u, v)));
  assert.ok(levelEquiv(max(u, v), max(v, u)));
  assert.ok(levelEquiv(imax(u, zero), zero));
  assert.ok(levelEquiv(imax(u, succ(v)), max(u, succ(v))));
  assert.ok(levelEquiv(imax(ofNat(1), zero), zero), "imax 1 0 is Prop");
  assert.ok(!levelEquiv(imax(u, v), max(u, v)), "imax u v differs from max u v when v = 0");
  assert.ok(geq(max(u, v), imax(u, v)));
  assert.ok(levelEquiv(imax(u, imax(v, u)), imax(v, u)) === bruteGeq(imax(u, imax(v, u)), imax(v, u)) && bruteGeq(imax(v, u), imax(u, imax(v, u))));
});

test("instantiation", () => {
  const l = max(u, imax(v, succ(u)));
  assert.ok(levelEquiv(instantiateLevel(l, [name("u"), name("v")], [ofNat(2), zero]), ofNat(3)));
});

test("geq agrees with brute force on random levels", () => {
  let seed = 12345;
  const rand = (n: number): number => {
    seed = (Math.imul(seed, 1103515245) + 12345) & 0x7fffffff;
    return seed % n;
  };
  const gen = (d: number): Level => {
    const k = d <= 0 ? rand(2) : rand(6);
    switch (k) {
      case 0:
        return zero;
      case 1:
        return [u, v, w][rand(3)]!;
      case 2:
        return succ(gen(d - 1));
      case 3:
        return max(gen(d - 1), gen(d - 1));
      default:
        return imax(gen(d - 1), gen(d - 1));
    }
  };
  for (let i = 0; i < 3000; i++) {
    const a = gen(3);
    const b = gen(3);
    assert.equal(geq(a, b), bruteGeq(a, b), `geq mismatch`);
  }
});
