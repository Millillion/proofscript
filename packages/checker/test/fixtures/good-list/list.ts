import { by, induction, omega, prove, simp, type nat, type Proof } from "proofscript";

export type Tree =
  | { readonly tag: "leaf" }
  | { readonly tag: "node"; readonly left: Tree; readonly value: nat; readonly right: Tree };

export function size(t: Tree): nat {
  switch (t.tag) {
    case "leaf":
      return 0;
    case "node":
      return size(t.left) + 1 + size(t.right);
  }
}

export function mirror(t: Tree): Tree {
  if (t.tag === "leaf") return t;
  return { tag: "node", left: mirror(t.right), value: t.value, right: mirror(t.left) };
}

export function size_mirror(t: Tree): Proof {
  return prove(
    size(mirror(t)) === size(t),
    by(induction(t, {
      leaf: () => simp(mirror),
      node: (_l, _v, _r, ihl, ihr) => by(simp(mirror, size, ihl, ihr), omega),
    })),
  );
}
