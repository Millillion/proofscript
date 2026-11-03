import assert from "node:assert/strict";
import { test } from "node:test";
import {
  abstract,
  app,
  bvar,
  constant,
  exprEq,
  fvar,
  hasLooseBVar,
  instantiate,
  instantiateRev,
  lam,
  liftLooseBVars,
  lowerLooseBVars,
  mkPi,
  pi,
  sort,
} from "../src/expr.ts";
import { zero } from "../src/level.ts";
import { name } from "../src/name.ts";

const Type = sort(zero);
const c = (s: string) => constant(name(s), []);

test("instantiate substitutes under binders and lifts the value", () => {
  // (fun x => #1 x)[#0 := f #3]  ==>  fun x => (f #4) x
  const body = lam(name("x"), Type, app(bvar(1), bvar(0)));
  const r = instantiate(body, [app(c("f"), bvar(3))]);
  assert.ok(exprEq(r, lam(name("x"), Type, app(app(c("f"), bvar(4)), bvar(0)))));
});

test("instantiate lowers higher loose variables", () => {
  const r = instantiate(app(bvar(0), bvar(2)), [c("a")]);
  assert.ok(exprEq(r, app(c("a"), bvar(1))));
});

test("abstract and instantiateRev are inverse", () => {
  const x = fvar(name("x"), Type);
  const y = fvar(name("y"), Type);
  const e = app(app(c("f"), x), lam(name("z"), Type, app(y, bvar(0))));
  const a = abstract(e, [x, y]);
  assert.equal(a.hasFVar, false);
  assert.ok(exprEq(instantiateRev(a, [x, y]), e));
  // y is the innermost: bvar 0 outside binders
  assert.ok(exprEq(a, app(app(c("f"), bvar(1)), lam(name("z"), Type, app(bvar(1), bvar(0))))));
});

test("lift and lower", () => {
  const e = lam(name("x"), Type, app(bvar(0), bvar(1)));
  assert.ok(exprEq(liftLooseBVars(e, 2), lam(name("x"), Type, app(bvar(0), bvar(3)))));
  assert.ok(exprEq(lowerLooseBVars(liftLooseBVars(e, 2), 2), e));
});

test("hasLooseBVar", () => {
  const e = lam(name("x"), Type, app(bvar(0), bvar(2)));
  assert.equal(hasLooseBVar(e, 1), true);
  assert.equal(hasLooseBVar(e, 0), false);
});

test("mkPi abstracts dependent binder types", () => {
  const A = fvar(name("A"), Type);
  const a = fvar(name("a"), A);
  const t = mkPi([A, a], A);
  assert.ok(exprEq(t, pi(name("A"), Type, pi(name("a"), bvar(0), bvar(1)))));
});

test("alpha equivalence ignores binder names and info", () => {
  assert.ok(exprEq(lam(name("x"), Type, bvar(0)), lam(name("y"), Type, bvar(0), "implicit")));
  assert.ok(!exprEq(lam(name("x"), Type, bvar(0)), pi(name("x"), Type, bvar(0))));
});
