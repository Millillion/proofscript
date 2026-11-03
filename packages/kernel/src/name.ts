// Hierarchical names (`Nat.add`, `_private.0.foo`), interned so that equality is
// pointer equality.

export type Name = AnonymousName | StrName | NumName;

export interface AnonymousName {
  readonly kind: "anonymous";
  readonly id: number;
}
export interface StrName {
  readonly kind: "str";
  readonly prefix: Name;
  readonly str: string;
  readonly id: number;
}
export interface NumName {
  readonly kind: "num";
  readonly prefix: Name;
  readonly num: bigint;
  readonly id: number;
}

let nextId = 1;
const table = new Map<string, Name>();

export const anonymous: AnonymousName = { kind: "anonymous", id: 0 };

export function strName(prefix: Name, str: string): Name {
  const key = `${prefix.id}s${str}`;
  let n = table.get(key);
  if (n === undefined) {
    n = { kind: "str", prefix, str, id: nextId++ };
    table.set(key, n);
  }
  return n;
}

export function numName(prefix: Name, num: bigint): Name {
  const key = `${prefix.id}n${num}`;
  let n = table.get(key);
  if (n === undefined) {
    n = { kind: "num", prefix, num, id: nextId++ };
    table.set(key, n);
  }
  return n;
}

/** Parses dotted syntax (`Nat.add`). Numeric components become `num` names. */
export function name(dotted: string): Name {
  let n: Name = anonymous;
  if (dotted === "") return n;
  for (const part of dotted.split(".")) {
    n = /^[0-9]+$/.test(part) ? numName(n, BigInt(part)) : strName(n, part);
  }
  return n;
}

export function nameToString(n: Name): string {
  switch (n.kind) {
    case "anonymous":
      return "[anonymous]";
    case "str":
      return n.prefix.kind === "anonymous" ? n.str : `${nameToString(n.prefix)}.${n.str}`;
    case "num":
      return n.prefix.kind === "anonymous" ? `${n.num}` : `${nameToString(n.prefix)}.${n.num}`;
  }
}
