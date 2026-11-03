import { by, exact, induction, simp, type nat, type Plus, type Prop } from "./proofscript/index.ts";

// An inductive family of propositions. `interface` + `declare namespace` emit no
// JavaScript. TS sees an opaque type; ProofScript sees
//   inductive Even : Nat → Prop | zero : Even 0 | step : Even k → Even (k + 2)
export interface Even<n extends nat> extends Prop {
  readonly __index: n;
}
export declare namespace Even {
  function zero(): Even<0>;
  function step<k extends nat>(h: Even<k>): Even<Plus<k, 2>>;
}

// Curry–Howard: when the claim is a type, it is the return type.
export function even_add<a extends nat, b extends nat>(ha: Even<a>, hb: Even<b>): Even<Plus<a, b>> {
  return by(induction(ha, {
    zero: () => exact(hb),
    step: (_h, ih) => by(simp(), exact(Even.step(ih))),
  }));
}
