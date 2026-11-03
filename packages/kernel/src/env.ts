// Declarations and the environment of checked constants.

import type { Expr } from "./expr.ts";
import { type Name, nameToString } from "./name.ts";

export type ReducibilityHints = { readonly kind: "opaque" } | { readonly kind: "abbrev" } | { readonly kind: "regular"; readonly height: number };

export type DefinitionSafety = "safe" | "unsafe" | "partial";

interface ConstantBase {
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
}

export interface AxiomInfo extends ConstantBase {
  readonly kind: "axiom";
  readonly isUnsafe: boolean;
}
export interface DefinitionInfo extends ConstantBase {
  readonly kind: "definition";
  readonly value: Expr;
  readonly hints: ReducibilityHints;
  readonly safety: DefinitionSafety;
  readonly all: readonly Name[];
}
export interface TheoremInfo extends ConstantBase {
  readonly kind: "theorem";
  readonly value: Expr;
  readonly all: readonly Name[];
}
export interface OpaqueInfo extends ConstantBase {
  readonly kind: "opaque";
  readonly value: Expr;
  readonly isUnsafe: boolean;
  readonly all: readonly Name[];
}
export type QuotKind = "type" | "ctor" | "lift" | "ind";
export interface QuotInfo extends ConstantBase {
  readonly kind: "quot";
  readonly quotKind: QuotKind;
}
export interface InductiveInfo extends ConstantBase {
  readonly kind: "inductive";
  readonly numParams: number;
  readonly numIndices: number;
  /** All types of the mutual block. */
  readonly all: readonly Name[];
  readonly ctors: readonly Name[];
  readonly numNested: number;
  readonly isRec: boolean;
  readonly isUnsafe: boolean;
  readonly isReflexive: boolean;
}
export interface ConstructorInfo extends ConstantBase {
  readonly kind: "constructor";
  readonly induct: Name;
  readonly cidx: number;
  readonly numParams: number;
  readonly numFields: number;
  readonly isUnsafe: boolean;
}
export interface RecursorRule {
  readonly ctor: Name;
  readonly nfields: number;
  readonly rhs: Expr;
}
export interface RecursorInfo extends ConstantBase {
  readonly kind: "recursor";
  readonly all: readonly Name[];
  readonly numParams: number;
  readonly numIndices: number;
  readonly numMotives: number;
  readonly numMinors: number;
  readonly rules: readonly RecursorRule[];
  readonly k: boolean;
  readonly isUnsafe: boolean;
}

export type ConstantInfo =
  | AxiomInfo
  | DefinitionInfo
  | TheoremInfo
  | OpaqueInfo
  | QuotInfo
  | InductiveInfo
  | ConstructorInfo
  | RecursorInfo;

export function isUnsafe(c: ConstantInfo): boolean {
  switch (c.kind) {
    case "definition":
      return c.safety === "unsafe";
    case "theorem":
    case "quot":
      return false;
    default:
      return c.isUnsafe;
  }
}

/** The declarations as they are submitted for checking (what Lean calls `Declaration`). */
export type Declaration =
  | { readonly kind: "axiom"; readonly info: AxiomInfo }
  | { readonly kind: "definition"; readonly info: DefinitionInfo }
  | { readonly kind: "theorem"; readonly info: TheoremInfo }
  | { readonly kind: "opaque"; readonly info: OpaqueInfo }
  | { readonly kind: "quot"; readonly infos: readonly QuotInfo[] }
  | {
      readonly kind: "inductive";
      readonly types: readonly InductiveInfo[];
      readonly ctors: readonly ConstructorInfo[];
      readonly recs: readonly RecursorInfo[];
    };

export class KernelError extends Error {
  override readonly name = "KernelError";
}

export class Environment {
  readonly #constants = new Map<Name, ConstantInfo>();
  readonly #parent: Environment | undefined;
  #quotInitialized = false;

  /** A child environment sees its parent's constants; additions stay in the child until `commit`. */
  constructor(parent?: Environment) {
    this.#parent = parent;
  }

  get quotInitialized(): boolean {
    return this.#quotInitialized || (this.#parent?.quotInitialized ?? false);
  }
  set quotInitialized(v: boolean) {
    this.#quotInitialized = v;
  }

  get(n: Name): ConstantInfo | undefined {
    return this.#constants.get(n) ?? this.#parent?.get(n);
  }

  /** Looks up a constant that must exist. */
  find(n: Name): ConstantInfo {
    const c = this.get(n);
    if (c === undefined) throw new KernelError(`unknown constant ${nameToString(n)}`);
    return c;
  }

  has(n: Name): boolean {
    return this.#constants.has(n) || (this.#parent?.has(n) ?? false);
  }

  /** Adds an already-checked constant. Only the checker should call this. */
  add(c: ConstantInfo): void {
    if (this.has(c.name)) throw new KernelError(`constant ${nameToString(c.name)} already declared`);
    this.#constants.set(c.name, c);
  }

  child(): Environment {
    return new Environment(this);
  }

  /** Moves a child's additions into its parent. */
  commit(): void {
    const p = this.#parent;
    if (p === undefined) throw new KernelError("cannot commit a root environment");
    for (const c of this.#constants.values()) p.add(c);
    if (this.#quotInitialized) p.quotInitialized = true;
    this.#constants.clear();
  }

  get size(): number {
    return this.#constants.size + (this.#parent?.size ?? 0);
  }

  ownValues(): IterableIterator<ConstantInfo> {
    return this.#constants.values();
  }
}
