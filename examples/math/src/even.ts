// An inductive family of propositions, and proofs by induction about it.
import { by, exact, induction, type nat, type Plus, type Prop, type Times } from "proofscript";

// inductive Even : Nat → Prop | zero : Even 0 | step : Even k → Even (k + 2)
export interface Even<n extends nat> extends Prop {
  readonly __index: n;
}
export declare namespace Even {
  function zero(): Even<0>;
  function step<k extends nat>(h: Even<k>): Even<Plus<k, 2>>;
}

// b + 0 and b + (k + 2) compute to b and (b + k) + 2, so constructors close both cases.
export function even_add<a extends nat, b extends nat>(ha: Even<a>, hb: Even<b>): Even<Plus<b, a>> {
  return by(induction(ha, {
    zero: () => exact(hb),
    step: (_h, ih) => exact(Even.step(ih)),
  }));
}

// 2 * (k + 1) computes to 2 * k + 2.
export function even_double(n: nat): Even<Times<2, typeof n>> {
  return by(induction(n, {
    zero: () => exact(Even.zero()),
    succ: (_k, ih) => exact(Even.step(ih)),
  }));
}
