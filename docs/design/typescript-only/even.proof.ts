import { by, exact, induction, type nat, type Plus, type Prop } from "./proofscript/index.ts";

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
// `b + 0` and `b + (k + 2)` reduce to `b` and `(b + k) + 2` by computation,
// so each case is closed by a constructor, with no arithmetic lemmas.
export function even_add<a extends nat, b extends nat>(ha: Even<a>, hb: Even<b>): Even<Plus<b, a>> {
  return by(induction(ha, {
    zero: () => exact(hb),
    step: (_h, ih) => exact(Even.step(ih)),
  }));
}
