// Translation of ProofScript (TypeScript) declarations into Lean 4 source.
//
// Lean is used as an untrusted proof engine (decision D30): theorems and the
// definitions they mention are translated to Lean, elaborated and proved there,
// exported, and then checked by ProofScript's own kernel.
//
// The translation of *definitions* is trusted until the adequacy work of phase
// 3: it must give each TypeScript function its JavaScript meaning. It therefore
// accepts only a small, explicitly supported subset and rejects everything else
// with a diagnostic. The translation of *proofs* is untrusted: whatever Lean
// produces is re-checked by the kernel.

import { relative } from "node:path";
import ts from "typescript6";
import { type Project, proofscriptName } from "./project.ts";

export interface Diagnostic {
  readonly file: string;
  readonly line: number;
  readonly column: number;
  readonly message: string;
}

export class TranslationError extends Error {
  readonly node: ts.Node;
  constructor(node: ts.Node, message: string) {
    super(message);
    this.node = node;
  }
}

export interface GeneratedDecl {
  readonly kind: "inductive" | "def" | "theorem";
  /** For generated proof obligations (postconditions): what they establish. */
  readonly obligation?: string;
  readonly tsName: string;
  readonly leanName: string;
  readonly node: ts.Node;
  readonly source: string;
  /** Lean names this declaration refers to (for ordering). */
  readonly deps: ReadonlySet<string>;
}

export interface Translation {
  readonly decls: GeneratedDecl[];
  readonly diagnostics: Diagnostic[];
  /** Refinement specs (pre/postconditions) present in the source but not verified yet. */
  readonly unverified: Diagnostic[];
}

/** ProofScript types that refine a carrier type (erased to the carrier in the logic for now). */
const REFINEMENTS = new Set(["Lt", "Le", "Gt", "Ge", "Length", "Is", "Simp"]);

type Mode = "value" | "prop";

/** A function declaration or a `const f = (…) => …` / `const f = function (…) {…}`. */
interface FnLike {
  readonly node: ts.FunctionDeclaration | ts.VariableDeclaration;
  readonly name: ts.Identifier;
  readonly typeParameters: ts.NodeArray<ts.TypeParameterDeclaration> | undefined;
  readonly parameters: ts.NodeArray<ts.ParameterDeclaration>;
  readonly type: ts.TypeNode | undefined;
  readonly body: ts.Block | ts.Expression | undefined;
  readonly isGeneratorOrAsync: boolean;
}

function fnLike(d: ts.Node | undefined): FnLike | undefined {
  if (d === undefined) return undefined;
  if (ts.isFunctionDeclaration(d) && d.name !== undefined) {
    return {
      node: d,
      name: d.name,
      typeParameters: d.typeParameters,
      parameters: d.parameters,
      type: d.type,
      body: d.body,
      isGeneratorOrAsync: d.asteriskToken !== undefined || (d.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword) ?? false),
    };
  }
  if (ts.isVariableDeclaration(d) && ts.isIdentifier(d.name) && d.initializer !== undefined) {
    const f = d.initializer;
    if (ts.isArrowFunction(f) || ts.isFunctionExpression(f)) {
      const list = d.parent;
      if (!ts.isVariableDeclarationList(list) || !(list.flags & ts.NodeFlags.Const)) return undefined;
      return {
        node: d,
        name: d.name,
        typeParameters: f.typeParameters,
        parameters: f.parameters,
        type: f.type,
        body: f.body,
        isGeneratorOrAsync: (ts.isFunctionExpression(f) && f.asteriskToken !== undefined) || (f.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword) ?? false),
      };
    }
  }
  return undefined;
}

interface Scope {
  /** Lean spelling for local symbols (parameters, callback parameters, `const`s, narrowed fields). */
  readonly locals: Map<ts.Symbol, string>;
  /** For variables narrowed to a constructor: field name -> Lean variable and declared type. */
  readonly narrowed: Map<ts.Symbol, Map<string, { lean: string; type: ts.TypeNode }>>;
}

interface InductiveShape {
  readonly leanName: string;
  readonly params: string[];
  readonly ctors: { tag: string; fields: { name: string; type: ts.TypeNode }[] }[];
}

const RESERVED = new Set([
  "fun", "λ", "let", "in", "if", "then", "else", "match", "with", "do", "by", "have", "show", "from", "at",
  "theorem", "def", "inductive", "structure", "where", "end", "namespace", "open", "import", "variable",
  "instance", "class", "example", "Type", "Prop", "Sort", "deriving", "mutual", "return", "for", "unless",
]);

export class Translator {
  readonly project: Project;
  readonly checker: ts.TypeChecker;
  readonly decls = new Map<ts.Node, GeneratedDecl>();
  readonly diagnostics: Diagnostic[] = [];
  readonly unverified: Diagnostic[] = [];
  readonly #inductives = new Map<ts.Node, InductiveShape>();
  readonly #inProgress = new Set<ts.Node>();
  /** Type parameters of the declaration being translated (for nested arrow functions). */
  #currentTypeParams = new Map<ts.Symbol, string>();
  #fresh = 0;

  constructor(project: Project) {
    this.project = project;
    this.checker = project.checker;
  }

  // ---- Entry point ---------------------------------------------------------------

  /** Translates every theorem in the given files, plus everything they depend on. */
  translateFiles(files: readonly ts.SourceFile[]): Translation {
    for (const sf of files) {
      for (const st of sf.statements) {
        if (ts.isFunctionDeclaration(st) && st.name !== undefined && (this.isTheorem(st) || this.hasSpec(st.type))) {
          this.#guard(() => this.requireDecl(st));
        }
        if (ts.isVariableStatement(st)) {
          for (const d of st.declarationList.declarations) {
            const fl = fnLike(d);
            if (fl !== undefined && this.hasSpec(fl.type)) this.#guard(() => this.requireDecl(d));
          }
        }
      }
    }
    return { decls: this.ordered(), diagnostics: this.diagnostics, unverified: this.unverified };
  }

  #guard(f: () => void): void {
    try {
      f();
    } catch (e) {
      if (e instanceof TranslationError) {
        const d = this.diag(e.node, e.message);
        if (!this.diagnostics.some((x) => x.file === d.file && x.line === d.line && x.column === d.column && x.message === d.message)) {
          this.diagnostics.push(d);
        }
      }
      else throw e;
    }
  }

  diag(node: ts.Node, message: string): Diagnostic {
    const sf = node.getSourceFile();
    const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
    return { file: sf.fileName, line: line + 1, column: character + 1, message };
  }

  fail(node: ts.Node, message: string): never {
    throw new TranslationError(node, message);
  }

  ordered(): GeneratedDecl[] {
    const all = [...this.decls.values()];
    const byName = new Map(all.map((d) => [d.leanName, d]));
    const out: GeneratedDecl[] = [];
    const state = new Map<string, "visiting" | "done">();
    const visit = (d: GeneratedDecl): void => {
      const s = state.get(d.leanName);
      if (s === "done") return;
      if (s === "visiting") return; // self-recursion; mutual recursion is rejected at translation
      state.set(d.leanName, "visiting");
      for (const dep of d.deps) {
        const t = byName.get(dep);
        if (t !== undefined && t !== d) visit(t);
      }
      state.set(d.leanName, "done");
      out.push(d);
    };
    for (const d of all) visit(d);
    return out;
  }

  // ---- Classification ----------------------------------------------------------------

  ps(node: ts.Node): string | undefined {
    const sym = ts.isIdentifier(node) || ts.isPropertyAccessExpression(node) || ts.isQualifiedName(node)
      ? this.checker.getSymbolAtLocation(node)
      : undefined;
    return proofscriptName(this.project, sym);
  }

  /** A theorem is a function whose body is `return prove(…)` or whose return type is a proposition. */
  isTheorem(fn: ts.FunctionDeclaration): boolean {
    const ret = this.singleReturn(fn);
    if (ret !== undefined && ts.isCallExpression(ret) && this.ps(ret.expression) === "prove") return true;
    if (fn.type !== undefined && this.isPropType(fn.type)) return true;
    return false;
  }

  /** A function with a refined return type (a postcondition) must be verified. */
  hasSpec(t: ts.TypeNode | undefined): boolean {
    return (
      t !== undefined &&
      ts.isIntersectionTypeNode(t) &&
      t.types.some((m) => ts.isTypeReferenceNode(m) && ["Lt", "Le", "Gt", "Ge", "Is"].includes(this.ps(m.typeName) ?? ""))
    );
  }

  singleReturn(fn: ts.FunctionDeclaration): ts.Expression | undefined {
    const body = fn.body;
    if (body === undefined || body.statements.length !== 1) return undefined;
    const st = body.statements[0]!;
    return ts.isReturnStatement(st) ? st.expression : undefined;
  }

  /** Whether a type node denotes a proposition (an interface extending ProofScript's `Prop`). */
  isPropType(t: ts.TypeNode): boolean {
    if (!ts.isTypeReferenceNode(t)) return false;
    const decl = this.declOf(t.typeName);
    return decl !== undefined && ts.isInterfaceDeclaration(decl) && this.extendsProp(decl);
  }

  extendsProp(decl: ts.InterfaceDeclaration): boolean {
    for (const h of decl.heritageClauses ?? []) {
      for (const t of h.types) if (this.ps(t.expression) === "Prop") return true;
    }
    return false;
  }

  declOf(node: ts.Node): ts.Declaration | undefined {
    let sym = this.checker.getSymbolAtLocation(node);
    if (sym === undefined) return undefined;
    if (sym.flags & ts.SymbolFlags.Alias) sym = this.checker.getAliasedSymbol(sym);
    return sym.declarations?.[0];
  }

  isUserDecl(d: ts.Node): boolean {
    const f = d.getSourceFile();
    return !f.isDeclarationFile && proofscriptName(this.project, undefined) === undefined && !/node_modules/.test(f.fileName);
  }

  // ---- Names ---------------------------------------------------------------------------

  moduleKey(sf: ts.SourceFile): string {
    const rel = relative(this.project.rootDir, sf.fileName).replace(/\.(m|c)?tsx?$/, "");
    return rel.split(/[\\/]/).map((p) => this.ident(p)).join(".");
  }

  ident(s: string): string {
    const clean = s.replace(/[^A-Za-z0-9_]/g, "_");
    const r = /^[0-9]/.test(clean) ? `_${clean}` : clean;
    return RESERVED.has(r) ? `«${r}»` : r;
  }

  leanNameOf(decl: ts.Node & { name?: ts.Node | undefined }): string {
    const n = decl.name !== undefined && ts.isIdentifier(decl.name) ? decl.name.text : "anonymous";
    return `PS.${this.moduleKey(decl.getSourceFile())}.${this.ident(n)}`;
  }

  freshVar(base: string): string {
    return `${this.ident(base)}_${++this.#fresh}`;
  }

  // ---- Declarations ----------------------------------------------------------------------

  /** Ensures the declaration is translated, returning its Lean name. */
  requireDecl(decl: ts.Declaration): string {
    const existing = this.decls.get(decl);
    if (existing !== undefined) return existing.leanName;
    if (ts.isTypeAliasDeclaration(decl)) return this.requireInductive(decl).leanName;
    if (ts.isInterfaceDeclaration(decl)) return this.translatePropInductive(decl);
    if (ts.isFunctionDeclaration(decl)) {
      const name = this.leanNameOf(decl);
      if (this.#inProgress.has(decl)) return name; // recursion
      this.#inProgress.add(decl);
      try {
        const g = this.isTheorem(decl) ? this.translateTheorem(decl) : this.translateFunction(fnLike(decl)!);
        this.decls.set(decl, g);
        return g.leanName;
      } finally {
        this.#inProgress.delete(decl);
      }
    }
    const fl = fnLike(decl);
    if (fl !== undefined) {
      const name = this.leanNameOf(decl as ts.VariableDeclaration);
      if (this.#inProgress.has(decl)) return name;
      this.#inProgress.add(decl);
      try {
        const g = this.translateFunction(fl);
        this.decls.set(decl, g);
        return g.leanName;
      } finally {
        this.#inProgress.delete(decl);
      }
    }
    return this.fail(decl, `ProofScript cannot use this declaration in the logic yet`);
  }

  // ---- Types ------------------------------------------------------------------------------

  /** Lean type for a TypeScript type node. `deps` collects referenced Lean declarations. */
  type(t: ts.TypeNode, deps: Set<string>, typeParams: Map<ts.Symbol, string>, verifiedRefinements = false): string {
    switch (t.kind) {
      case ts.SyntaxKind.BooleanKeyword:
        return "Bool";
      case ts.SyntaxKind.StringKeyword:
        return "String";
      case ts.SyntaxKind.BigIntKeyword:
        return "Int";
      case ts.SyntaxKind.NumberKeyword:
        return this.fail(t, "`number` (IEEE-754 floating point) is not supported in the logic yet; use `int` or `nat`");
      case ts.SyntaxKind.ParenthesizedType:
        return this.type((t as ts.ParenthesizedTypeNode).type, deps, typeParams);
      case ts.SyntaxKind.LiteralType: {
        const lit = (t as ts.LiteralTypeNode).literal;
        if (ts.isNumericLiteral(lit)) return lit.text;
        return this.fail(t, "unsupported literal type");
      }
      default:
        break;
    }
    if (ts.isTypeReferenceNode(t)) {
      const ps = this.ps(t.typeName);
      const args = (t.typeArguments ?? []).map((a) => this.type(a, deps, typeParams));
      switch (ps) {
        case "nat":
        case "Nat":
          return "Nat";
        case "int":
        case "Int":
          return "Int";
        case "Plus":
          return `(${args[0]} + ${args[1]})`;
        case "Times":
          return `(${args[0]} * ${args[1]})`;
        case undefined:
          break;
        default:
          return this.fail(t, `ProofScript type ${ps} is not supported here yet`);
      }
      const sym = this.checker.getSymbolAtLocation(t.typeName);
      if (sym !== undefined && typeParams.has(sym)) return typeParams.get(sym)!;
      if (sym !== undefined && this.#currentTypeParams.has(sym)) return this.#currentTypeParams.get(sym)!;
      const decl = this.declOf(t.typeName);
      if (decl !== undefined && (ts.isTypeAliasDeclaration(decl) || ts.isInterfaceDeclaration(decl))) {
        const ln = this.requireDecl(decl);
        deps.add(ln);
        return args.length === 0 ? ln : `(${ln} ${args.join(" ")})`;
      }
    }
    if (ts.isIntersectionTypeNode(t)) {
      const carrier = t.types.filter((m) => !(ts.isTypeReferenceNode(m) && REFINEMENTS.has(this.ps(m.typeName) ?? "")));
      if (carrier.length !== 1) return this.fail(t, "unsupported intersection type");
      for (const m of t.types) {
        if (!verifiedRefinements && m !== carrier[0] && !(ts.isTypeReferenceNode(m) && this.ps(m.typeName) === "Simp")) {
          const d = this.diag(m, `precondition \`${m.getText()}\` is not yet checked at call sites (it is assumed when proving this function's postconditions)`);
          if (!this.unverified.some((x) => x.file === d.file && x.line === d.line && x.column === d.column)) this.unverified.push(d);
        }
      }
      return this.type(carrier[0]!, deps, typeParams);
    }
    if (ts.isTypeQueryNode(t)) {
      // `typeof x` in an index position: the value x itself.
      return this.fail(t, "`typeof x` value indices are not supported by the Lean engine yet");
    }
    if (ts.isArrayTypeNode(t) || (ts.isTypeOperatorNode(t) && ts.isArrayTypeNode(t.type))) {
      return this.fail(t, "arrays are not supported in the logic yet (milestone M5)");
    }
    return this.fail(t, `unsupported type ${t.getText()}`);
  }

  typeParamBinders(
    tps: ts.NodeArray<ts.TypeParameterDeclaration> | undefined,
    deps: Set<string>,
    typeParams: Map<ts.Symbol, string>,
  ): string[] {
    const out: string[] = [];
    for (const tp of tps ?? []) {
      const sym = this.checker.getSymbolAtLocation(tp.name);
      const n = this.ident(tp.name.text);
      if (sym !== undefined) typeParams.set(sym, n);
      if (tp.constraint !== undefined) {
        // `n extends nat`: a ghost value parameter.
        out.push(`{${n} : ${this.type(tp.constraint, deps, typeParams)}}`);
      } else {
        out.push(`{${n} : Type}`);
      }
    }
    return out;
  }

  // ---- Inductive types: discriminated unions ------------------------------------------------

  requireInductive(decl: ts.TypeAliasDeclaration): InductiveShape {
    const cached = this.#inductives.get(decl);
    if (cached !== undefined) return cached;
    const leanName = this.leanNameOf(decl);
    if (ts.isIntersectionTypeNode(decl.type) || ts.isArrayTypeNode(decl.type) || ts.isTypeOperatorNode(decl.type)) {
      return this.fail(decl, "refinement type aliases and arrays are not supported in the logic yet (milestone M5)");
    }
    const members = ts.isUnionTypeNode(decl.type) ? decl.type.types : [decl.type];
    const ctors: InductiveShape["ctors"] = [];
    for (const m of members) {
      if (!ts.isTypeLiteralNode(m)) return this.fail(m, "only discriminated unions of object types (with a `tag` field) can be inductive types");
      let tag: string | undefined;
      const fields: { name: string; type: ts.TypeNode }[] = [];
      for (const p of m.members) {
        if (!ts.isPropertySignature(p) || p.type === undefined || !ts.isIdentifier(p.name)) return this.fail(p, "unsupported member");
        if (p.questionToken !== undefined) return this.fail(p, "optional fields are not supported in inductive types");
        if (!p.modifiers?.some((mod) => mod.kind === ts.SyntaxKind.ReadonlyKeyword)) {
          return this.fail(p, "fields of inductive types must be `readonly` (mutable data is not part of the logic)");
        }
        if (p.name.text === "tag") {
          if (!ts.isLiteralTypeNode(p.type) || !ts.isStringLiteral(p.type.literal)) return this.fail(p, "`tag` must be a string literal type");
          tag = p.type.literal.text;
        } else {
          fields.push({ name: p.name.text, type: p.type });
        }
      }
      if (tag === undefined) return this.fail(m, "each member of an inductive type needs a `readonly tag` string literal");
      if (ctors.some((c) => c.tag === tag)) return this.fail(m, `duplicate tag "${tag}"`);
      ctors.push({ tag, fields });
    }
    const params = (decl.typeParameters ?? []).map((tp) => this.ident(tp.name.text));
    const shape: InductiveShape = { leanName, params, ctors };
    this.#inductives.set(decl, shape);
    try {
      this.#emitInductive(decl, shape);
    } catch (e) {
      this.#inductives.delete(decl);
      this.decls.delete(decl);
      throw e;
    }
    return shape;
  }

  #emitInductive(decl: ts.TypeAliasDeclaration, shape: InductiveShape): void {
    const { leanName, params, ctors } = shape;
    // Register before translating field types (they may refer to the type itself).
    const placeholder: GeneratedDecl = { kind: "inductive", tsName: decl.name.text, leanName, node: decl, source: "", deps: new Set() };
    this.decls.set(decl, placeholder);
    const deps = new Set<string>();
    const typeParams = new Map<ts.Symbol, string>();
    for (const tp of decl.typeParameters ?? []) {
      const sym = this.checker.getSymbolAtLocation(tp.name);
      if (sym !== undefined) typeParams.set(sym, this.ident(tp.name.text));
    }
    const self = params.length === 0 ? leanName : `(${leanName} ${params.join(" ")})`;
    const lines = [`inductive ${leanName}${params.map((p) => ` (${p} : Type)`).join("")} where`];
    for (const c of ctors) {
      const fs = c.fields.map((f) => ` (${this.ident(f.name)} : ${this.type(f.type, deps, typeParams)})`).join("");
      lines.push(`  | ${this.ident(c.tag)}${fs} : ${self}`);
    }
    deps.delete(leanName);
    this.decls.set(decl, { ...placeholder, source: lines.join("\n"), deps });
  }

  shapeOfType(t: ts.Type): InductiveShape | undefined {
    const decl = t.aliasSymbol?.declarations?.[0];
    if (decl !== undefined && ts.isTypeAliasDeclaration(decl)) return this.#inductives.get(decl) ?? this.requireInductive(decl);
    return undefined;
  }

  // ---- Inductive propositions: interface extends Prop + declare namespace -------------------

  translatePropInductive(decl: ts.InterfaceDeclaration): string {
    if (!this.extendsProp(decl)) return this.fail(decl, "only interfaces extending ProofScript's `Prop` can be used in the logic");
    const leanName = this.leanNameOf(decl);
    const existing = this.decls.get(decl);
    if (existing !== undefined) return existing.leanName;
    const placeholder: GeneratedDecl = { kind: "inductive", tsName: decl.name.text, leanName, node: decl, source: "", deps: new Set() };
    this.decls.set(decl, placeholder);
    try {
      return this.#emitPropInductive(decl, leanName, placeholder);
    } catch (e) {
      this.decls.delete(decl);
      throw e;
    }
  }

  #emitPropInductive(decl: ts.InterfaceDeclaration, leanName: string, placeholder: GeneratedDecl): string {
    const deps = new Set<string>();
    const indexTypes: string[] = [];
    const typeParams = new Map<ts.Symbol, string>();
    for (const tp of decl.typeParameters ?? []) {
      if (tp.constraint === undefined) return this.fail(tp, "indices of inductive propositions must have a type (`n extends nat`)");
      indexTypes.push(this.type(tp.constraint, deps, typeParams));
    }
    // Constructors: functions in a `declare namespace` with the same name.
    const sym = this.checker.getSymbolAtLocation(decl.name);
    const ns = sym?.declarations?.find((d): d is ts.ModuleDeclaration => ts.isModuleDeclaration(d));
    if (ns === undefined || ns.body === undefined || !ts.isModuleBlock(ns.body)) {
      return this.fail(decl, `inductive proposition ${decl.name.text} needs a \`declare namespace ${decl.name.text}\` listing its constructors`);
    }
    const lines = [`inductive ${leanName} : ${[...indexTypes, "Prop"].join(" → ")} where`];
    for (const st of ns.body.statements) {
      if (!ts.isFunctionDeclaration(st) || st.name === undefined || st.type === undefined) return this.fail(st, "constructors must be function signatures");
      const tps = new Map<ts.Symbol, string>();
      const binders = this.typeParamBinders(st.typeParameters, deps, tps);
      for (const p of st.parameters) {
        if (!ts.isIdentifier(p.name) || p.type === undefined) return this.fail(p, "constructor parameters need names and types");
        binders.push(`(${this.ident(p.name.text)} : ${this.type(p.type, deps, tps)})`);
      }
      lines.push(`  | ${this.ident(st.name.text)}${binders.map((b) => ` ${b}`).join("")} : ${this.type(st.type, deps, tps)}`);
    }
    deps.delete(leanName);
    this.decls.set(decl, { ...placeholder, source: lines.join("\n"), deps });
    return leanName;
  }

  // ---- Functions -------------------------------------------------------------------------------

  translateFunction(fn: FnLike): GeneratedDecl {
    const leanName = this.leanNameOf(fn.node);
    if (fn.body === undefined) return this.fail(fn.node, "functions used in the logic need a body");
    let inferredBool = false;
    if (fn.type === undefined) {
      // An unannotated return type is accepted only when TypeScript infers `boolean`
      // (numbers are ambiguous: `nat`, `int` or IEEE-754 `number`).
      const sig = this.checker.getSignatureFromDeclaration(ts.isVariableDeclaration(fn.node) ? (fn.node.initializer as ts.SignatureDeclaration) : fn.node);
      const rt = sig === undefined ? undefined : this.checker.getReturnTypeOfSignature(sig);
      if (rt === undefined || !(rt.flags & ts.TypeFlags.BooleanLike)) {
        return this.fail(fn.node, "functions used in the logic need a declared return type (only `boolean` may be left to inference)");
      }
      inferredBool = true;
    }
    if (fn.isGeneratorOrAsync) return this.fail(fn.node, "generators and async functions cannot be used in the logic");
    const deps = new Set<string>();
    const scope: Scope = { locals: new Map(), narrowed: new Map() };
    const typeParams = new Map<ts.Symbol, string>();
    const binders = this.typeParamBinders(fn.typeParameters, deps, typeParams);
    fn.parameters.forEach((p, i) => {
      if (!ts.isIdentifier(p.name) || p.type === undefined || p.initializer !== undefined || p.dotDotDotToken !== undefined) {
        return this.fail(p, "parameters of functions used in the logic need a plain name and a type");
      }
      const n = this.ident(p.name.text);
      const sym = this.checker.getSymbolAtLocation(p.name);
      if (sym !== undefined) scope.locals.set(sym, n);
      binders.push(`(${n} : ${this.type(p.type, deps, typeParams, true)})`);
      binders.push(...this.preconditionBinders(p, n, i, scope, deps, typeParams));
      return undefined;
    });
    const ret = inferredBool ? "Bool" : this.type(fn.type!, deps, typeParams, true);
    const body = ts.isBlock(fn.body) ? this.statements(fn.body.statements, 0, scope, deps, fn.node) : this.expr(fn.body, "value", scope, deps);
    const recursive = deps.has(leanName);
    deps.delete(leanName);
    const source = `def ${leanName}${binders.map((b) => ` ${b}`).join("")} : ${ret} :=\n  ${indent(body, 2)}`;
    const def: GeneratedDecl = { kind: "def", tsName: fn.name.text, leanName, node: fn.node, source, deps };
    this.decls.set(fn.node, def);
    this.#postconditions(fn, def, binders, scope, typeParams, recursive);
    return def;
  }

  /**
   * Preconditions: each refinement of a parameter becomes a proof argument with a
   * default tactic (a Lean autoParam), so every call site must prove it, in its own
   * context (including the conditions of enclosing `if`s).
   */
  preconditionBinders(p: ts.ParameterDeclaration, n: string, i: number, scope: Scope, deps: Set<string>, typeParams: Map<ts.Symbol, string>): string[] {
    if (p.type === undefined || !ts.isIntersectionTypeNode(p.type)) return [];
    const out: string[] = [];
    p.type.types.forEach((m, k) => {
      const prop = this.refinementProp(m, n, scope, deps, typeParams);
      if (prop !== undefined) out.push(`(pre_${i}_${k} : ${prop} := by first | omega | (simp_all <;> omega) | decide)`);
    });
    return out;
  }

  /** The proposition a refinement type asserts of `subject`, or undefined if `m` is the carrier. */
  refinementProp(m: ts.TypeNode, subject: string, scope: Scope, deps: Set<string>, typeParams: Map<ts.Symbol, string>): string | undefined {
    if (!ts.isTypeReferenceNode(m)) return undefined;
    const kind = this.ps(m.typeName);
    const args = m.typeArguments ?? [];
    const value = (t: ts.TypeNode): string => {
      if (ts.isTypeQueryNode(t) && ts.isIdentifier(t.exprName)) return this.local(t.exprName, scope);
      if (ts.isLiteralTypeNode(t) && ts.isNumericLiteral(t.literal)) return t.literal.text;
      return this.type(t, deps, typeParams);
    };
    switch (kind) {
      case "Lt":
        return `${subject} < ${value(args[0]!)}`;
      case "Le":
        return `${subject} ≤ ${value(args[0]!)}`;
      case "Gt":
        return `${subject} > ${value(args[0]!)}`;
      case "Ge":
        return `${subject} ≥ ${value(args[0]!)}`;
      case "Is": {
        const pred = args[0];
        if (pred === undefined || !ts.isTypeQueryNode(pred) || !ts.isIdentifier(pred.exprName)) return this.fail(m, "`Is` takes `typeof predicate`");
        const decl = this.declOf(pred.exprName);
        if (decl === undefined || fnLike(decl) === undefined) return this.fail(pred, "predicates in `Is` must be functions declared in your project");
        const pn = this.requireDecl(decl);
        deps.add(pn);
        const extra = args[1] === undefined ? [] : ts.isTupleTypeNode(args[1]) ? args[1].elements.map((e) => value(e as ts.TypeNode)) : this.fail(args[1], "expected a tuple of arguments");
        return `${pn} ${subject}${extra.map((x) => ` ${x}`).join("")} = true`;
      }
      default:
        return undefined;
    }
  }

  #postconditions(
    fn: FnLike,
    def: GeneratedDecl,
    binders: string[],
    scope: Scope,
    typeParams: Map<ts.Symbol, string>,
    recursive: boolean,
  ): void {
    const rt = fn.type;
    if (rt === undefined || !ts.isIntersectionTypeNode(rt)) return;
    const args = fn.parameters.map((p) => this.local(p.name as ts.Identifier, scope));
    const call = `(${def.leanName}${args.map((a) => ` ${a}`).join("")})`;
    const allArgs = binders.map((b) => /^[({]([^ ]+) :/.exec(b)?.[1]).filter((x): x is string => x !== undefined && !b0IsType(x, binders));
    rt.types.forEach((m, i) => {
      this.#guard(() => {
        const deps = new Set<string>([def.leanName]);
        const prop = this.refinementProp(m, call, scope, deps, typeParams);
        if (prop === undefined) return;
        const simpSet = [def.leanName, ...this.#defClosure(deps, def.leanName)].join(", ");
        const tac = recursive
          ? `fun_induction ${def.leanName}${allArgs.map((a) => ` ${a}`).join("")} <;> simp_all [${simpSet}] <;> (try omega)`
          : `simp_all [${simpSet}] <;> (try omega)`;
        const leanName = `${def.leanName}.post_${i}`;
        const source = `@[simp] theorem ${leanName}${binders.map((b) => ` ${b}`).join("")} :\n    ${prop} := by\n  ${tac}`;
        const key = m as ts.Node;
        this.decls.set(key, {
          kind: "theorem",
          tsName: `${def.tsName} (postcondition \`${m.getText()}\`)`,
          leanName,
          node: m,
          source,
          deps,
          obligation: `postcondition of ${def.tsName}`,
        });
      });
    });
  }

  /** Definitions reachable from `roots` (for unfolding in automatic proofs). */
  #defClosure(roots: Iterable<string>, exclude: string): string[] {
    const byName = new Map([...this.decls.values()].map((d) => [d.leanName, d]));
    const out = new Set<string>();
    const stack = [...roots];
    while (stack.length > 0) {
      const n = stack.pop()!;
      const d = byName.get(n);
      if (d === undefined || d.kind !== "def" || out.has(n)) continue;
      if (n !== exclude) out.add(n);
      stack.push(...d.deps);
    }
    return [...out];
  }



  /** Translates a statement list that must end in `return` on every path. */
  statements(sts: readonly ts.Statement[], i: number, scope: Scope, deps: Set<string>, ctx: ts.Node): string {
    const st = sts[i];
    if (st === undefined) return this.fail(ctx, "every path must end in `return`");
    if (ts.isReturnStatement(st)) {
      if (st.expression === undefined) return this.fail(st, "`return` needs a value");
      return this.expr(st.expression, "value", scope, deps);
    }
    if (ts.isVariableStatement(st)) {
      const list = st.declarationList;
      if (!(list.flags & ts.NodeFlags.Const)) return this.fail(st, "only `const` declarations are supported in functions used in the logic (loops and mutation come later)");
      let out = "";
      for (const d of list.declarations) {
        if (!ts.isIdentifier(d.name) || d.initializer === undefined) return this.fail(d, "unsupported declaration");
        const n = this.freshVar(d.name.text);
        const v = this.expr(d.initializer, "value", scope, deps);
        const sym = this.checker.getSymbolAtLocation(d.name);
        if (sym !== undefined) scope.locals.set(sym, n);
        out += `let ${n} := ${v}\n`;
      }
      return out + this.statements(sts, i + 1, scope, deps, ctx);
    }
    if (ts.isIfStatement(st)) {
      const rest = (s: Scope) => this.statements(sts, i + 1, s, deps, ctx);
      const thenBranch = (s: Scope) => this.statements(blockStatements(st.thenStatement), 0, s, deps, st);
      const elseBranch =
        st.elseStatement === undefined
          ? rest
          : (s: Scope) => this.statements([...blockStatements(st.elseStatement!), ...sts.slice(i + 1)], 0, s, deps, ctx);
      // `if (…) return a; rest` and `if (…) {…} else {…}`.
      const thenTerminates = endsInReturn(st.thenStatement);
      if (!thenTerminates && st.elseStatement === undefined) return this.fail(st, "an `if` without `else` must end in `return`");
      return this.branch(st.expression, thenBranch, elseBranch, scope, deps);
    }
    if (ts.isSwitchStatement(st)) return this.switchStatement(st, scope, deps);
    if (ts.isBlock(st)) return this.statements([...st.statements, ...sts.slice(i + 1)], 0, scope, deps, ctx);
    return this.fail(st, "this statement is not supported in functions used in the logic yet");
  }

  switchStatement(st: ts.SwitchStatement, scope: Scope, deps: Set<string>): string {
    const disc = this.tagDiscriminant(st.expression);
    if (disc === undefined) return this.fail(st.expression, "only `switch (x.tag)` over a discriminated union is supported");
    const arms = new Map<string, readonly ts.Statement[]>();
    let deflt: readonly ts.Statement[] | undefined;
    for (const clause of st.caseBlock.clauses) {
      if (ts.isCaseClause(clause)) {
        if (!ts.isStringLiteral(clause.expression)) return this.fail(clause, "case labels must be string literals");
        arms.set(clause.expression.text, clause.statements);
      } else {
        deflt = clause.statements;
      }
    }
    return this.match(disc, (tag) => arms.get(tag) ?? deflt, scope, deps, st, "value", (sts, s) => this.statements(sts, 0, s, deps, st));
  }

  // ---- Branching on discriminated unions ------------------------------------------------------

  /** If `e` is `x.tag` for a variable `x` of an inductive type, returns `x`. */
  tagDiscriminant(e: ts.Expression): ts.Identifier | undefined {
    if (ts.isPropertyAccessExpression(e) && e.name.text === "tag" && ts.isIdentifier(e.expression)) {
      const shape = this.shapeOfType(this.checker.getTypeAtLocation(e.expression));
      if (shape !== undefined) return e.expression;
    }
    return undefined;
  }

  /** `x.tag === "K"` / `x.tag !== "K"`: returns the variable, the tag and polarity. */
  tagTest(e: ts.Expression): { x: ts.Identifier; tag: string; positive: boolean } | undefined {
    if (ts.isParenthesizedExpression(e)) return this.tagTest(e.expression);
    if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) {
      const t = this.tagTest(e.operand);
      return t === undefined ? undefined : { ...t, positive: !t.positive };
    }
    if (!ts.isBinaryExpression(e)) return undefined;
    const op = e.operatorToken.kind;
    if (op !== ts.SyntaxKind.EqualsEqualsEqualsToken && op !== ts.SyntaxKind.ExclamationEqualsEqualsToken) return undefined;
    let x = this.tagDiscriminant(e.left);
    let lit: ts.Expression = e.right;
    if (x === undefined) {
      x = this.tagDiscriminant(e.right);
      lit = e.left;
    }
    if (x === undefined || !ts.isStringLiteral(lit)) return undefined;
    return { x, tag: lit.text, positive: op === ts.SyntaxKind.EqualsEqualsEqualsToken };
  }

  /** Generates a `match` on `x` with one arm per constructor, narrowing `x` in each arm. */
  match<T>(
    x: ts.Identifier,
    armFor: (tag: string) => T | undefined,
    scope: Scope,
    deps: Set<string>,
    node: ts.Node,
    _mode: Mode,
    gen: (t: T, s: Scope) => string,
  ): string {
    const shape = this.shapeOfType(this.checker.getTypeAtLocation(x))!;
    deps.add(shape.leanName);
    const sym = this.checker.getSymbolAtLocation(x)!;
    const xs = this.local(x, scope);
    const lines = [`match ${xs} with`];
    for (const c of shape.ctors) {
      const arm = armFor(c.tag);
      if (arm === undefined) return this.fail(node, `missing case for "${c.tag}"`);
      const fields = new Map<string, { lean: string; type: ts.TypeNode }>();
      const vars = c.fields.map((f) => {
        const v = this.freshVar(f.name);
        fields.set(f.name, { lean: v, type: f.type });
        return v;
      });
      const narrowed = new Map(scope.narrowed);
      narrowed.set(sym, fields);
      const body = gen(arm, { locals: scope.locals, narrowed });
      lines.push(`| .${this.ident(c.tag)}${vars.map((v) => ` ${v}`).join("")} =>\n  ${indent(body, 2)}`);
    }
    return lines.join("\n");
  }

  branch(cond: ts.Expression, a: (s: Scope) => string, b: (s: Scope) => string, scope: Scope, deps: Set<string>): string {
    const t = this.tagTest(cond);
    if (t !== undefined) {
      return this.match(t.x, (tag) => ((tag === t.tag) === t.positive ? a : b), scope, deps, cond, "value", (f, s) => f(s));
    }
    // Dependent `if`: each branch has its condition (or its negation) as a hypothesis,
    // which precondition and subtraction side conditions can use.
    const c = this.expr(cond, "prop", scope, deps);
    const h = this.freshVar("h");
    return `if ${h} : ${c} then\n  ${indent(a(scope), 2)}\nelse\n  ${indent(b(scope), 2)}`;
  }

  local(id: ts.Identifier, scope: Scope): string {
    const sym = this.checker.getSymbolAtLocation(id);
    const l = sym === undefined ? undefined : scope.locals.get(sym);
    if (l === undefined) return this.fail(id, `unknown variable ${id.text}`);
    return l;
  }

  // ---- Expressions ---------------------------------------------------------------------------

  isBooleanType(e: ts.Expression): boolean {
    return (this.checker.getTypeAtLocation(e).flags & ts.TypeFlags.BooleanLike) !== 0;
  }

  expr(e: ts.Expression, mode: Mode, scope: Scope, deps: Set<string>): string {
    if (ts.isParenthesizedExpression(e)) return `(${this.expr(e.expression, mode, scope, deps)})`;
    if (ts.isNumericLiteral(e)) {
      if (!/^[0-9]+$/.test(e.text)) return this.fail(e, "only non-negative integer literals are supported in the logic yet");
      return e.text;
    }
    if (ts.isBigIntLiteral(e)) return `(${e.text.slice(0, -1)} : Int)`;
    if (e.kind === ts.SyntaxKind.TrueKeyword) return mode === "prop" ? "True" : "true";
    if (e.kind === ts.SyntaxKind.FalseKeyword) return mode === "prop" ? "False" : "false";
    if (ts.isStringLiteral(e)) return JSON.stringify(e.text);
    if (ts.isIdentifier(e)) {
      const sym = this.checker.getSymbolAtLocation(e);
      const l = sym === undefined ? undefined : scope.locals.get(sym);
      if (l !== undefined) return this.coerceProp(e, l, mode);
      const ps = this.ps(e);
      if (ps !== undefined) return this.fail(e, `ProofScript's ${ps} cannot be used as a value here`);
      const decl = this.declOf(e);
      if (decl !== undefined && fnLike(decl) !== undefined) {
        const ln = this.requireDecl(decl);
        deps.add(ln);
        return ln;
      }
      return this.fail(e, `unknown name ${e.text}`);
    }
    if (ts.isPropertyAccessExpression(e)) {
      if (ts.isIdentifier(e.expression)) {
        const sym = this.checker.getSymbolAtLocation(e.expression);
        const fields = sym === undefined ? undefined : scope.narrowed.get(sym);
        if (fields !== undefined) {
          const f = fields.get(e.name.text);
          if (f === undefined) return this.fail(e, `field ${e.name.text} does not exist on this constructor`);
          return this.coerceProp(e, f.lean, mode);
        }
        const shape = this.shapeOfType(this.checker.getTypeAtLocation(e.expression));
        if (shape !== undefined && e.name.text !== "tag") {
          // A single-constructor type (a structure): fields are always available.
          if (shape.ctors.length === 1) {
            const c = shape.ctors[0]!;
            const idx = c.fields.findIndex((f) => f.name === e.name.text);
            if (idx < 0) return this.fail(e, `no field ${e.name.text}`);
            deps.add(shape.leanName);
            const vars = c.fields.map((f) => this.freshVar(f.name));
            const r = `(match ${this.local(e.expression, scope)} with | .${this.ident(c.tag)}${vars.map((v) => ` ${v}`).join("")} => ${vars[idx]})`;
            return this.coerceProp(e, r, mode);
          }
          return this.fail(e, `\`${e.getText()}\` needs a check of \`${e.expression.text}.tag\` first`);
        }
      }
      return this.fail(e, "unsupported property access");
    }
    if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) {
      const inner = this.expr(e.operand, mode, scope, deps);
      return mode === "prop" ? `¬(${inner})` : `!(${inner})`;
    }
    if (ts.isConditionalExpression(e)) {
      if (mode === "prop") return this.fail(e, "conditional expressions are not supported in statements yet");
      return this.branch(e.condition, (s) => this.expr(e.whenTrue, "value", s, deps), (s) => this.expr(e.whenFalse, "value", s, deps), scope, deps);
    }
    if (ts.isBinaryExpression(e)) return this.binary(e, mode, scope, deps);
    if (ts.isCallExpression(e)) return this.call(e, mode, scope, deps);
    if (ts.isObjectLiteralExpression(e)) return this.objectLiteral(e, scope, deps);
    if (ts.isArrowFunction(e)) return this.fail(e, "functions as values are not supported here yet");
    return this.fail(e, `unsupported expression`);
  }

  coerceProp(e: ts.Expression, s: string, mode: Mode): string {
    return mode === "prop" && this.isBooleanType(e) ? `(${s} = true)` : s;
  }

  binary(e: ts.BinaryExpression, mode: Mode, scope: Scope, deps: Set<string>): string {
    const k = e.operatorToken.kind;
    const sub = (x: ts.Expression, m: Mode) => this.expr(x, m, scope, deps);
    const tagT = this.tagTest(e);
    if (tagT !== undefined) {
      const x = this.local(tagT.x, scope);
      const r = `(match ${x} with | .${this.ident(tagT.tag)} .. => true | _ => false)`;
      const v = tagT.positive ? r : `!${r}`;
      return mode === "prop" ? `(${v} = true)` : v;
    }
    switch (k) {
      case ts.SyntaxKind.AmpersandAmpersandToken:
        return mode === "prop" ? `(${sub(e.left, "prop")} ∧ ${sub(e.right, "prop")})` : `(${sub(e.left, "value")} && ${sub(e.right, "value")})`;
      case ts.SyntaxKind.BarBarToken:
        return mode === "prop" ? `(${sub(e.left, "prop")} ∨ ${sub(e.right, "prop")})` : `(${sub(e.left, "value")} || ${sub(e.right, "value")})`;
      case ts.SyntaxKind.EqualsEqualsEqualsToken:
        this.requireEqualityType(e);
        return mode === "prop" ? `(${sub(e.left, "value")} = ${sub(e.right, "value")})` : `(${sub(e.left, "value")} == ${sub(e.right, "value")})`;
      case ts.SyntaxKind.ExclamationEqualsEqualsToken:
        this.requireEqualityType(e);
        return mode === "prop" ? `(${sub(e.left, "value")} ≠ ${sub(e.right, "value")})` : `(${sub(e.left, "value")} != ${sub(e.right, "value")})`;
      case ts.SyntaxKind.LessThanToken:
      case ts.SyntaxKind.LessThanEqualsToken:
      case ts.SyntaxKind.GreaterThanToken:
      case ts.SyntaxKind.GreaterThanEqualsToken: {
        const op = { [ts.SyntaxKind.LessThanToken]: "<", [ts.SyntaxKind.LessThanEqualsToken]: "≤", [ts.SyntaxKind.GreaterThanToken]: ">", [ts.SyntaxKind.GreaterThanEqualsToken]: "≥" }[k];
        const r = `(${sub(e.left, "value")} ${op} ${sub(e.right, "value")})`;
        return mode === "prop" ? r : `(decide ${r})`;
      }
      case ts.SyntaxKind.PlusToken:
      case ts.SyntaxKind.AsteriskToken:
      case ts.SyntaxKind.MinusToken: {
        this.requireIntegerType(e, scope);
        const op = k === ts.SyntaxKind.PlusToken ? "+" : k === ts.SyntaxKind.AsteriskToken ? "*" : "-";
        const l = sub(e.left, "value");
        const r = sub(e.right, "value");
        if (op === "-" && this.isNatExpr(e.left, scope)) {
          // In JavaScript the result could be negative; in Lean, Nat subtraction would
          // silently truncate. So the subtraction is only allowed where it is proved
          // not to go below zero.
          return `(have _ : ${r} ≤ ${l} := (by first | omega | (simp_all <;> omega) | decide); ${l} - ${r})`;
        }
        return `(${l} ${op} ${r})`;
      }
      default:
        return this.fail(e.operatorToken, `operator ${e.operatorToken.getText()} is not supported in the logic yet`);
    }
  }

  isNatExpr(e: ts.Expression, scope: Scope): boolean {
    return this.kindOf(e, scope) === "nat";
  }

  /**
   * The logical kind of an expression, from declared types. TypeScript erases
   * `nat`/`int` to `number` in its own types, so the declarations are consulted.
   */
  kindOf(e: ts.Expression, scope: Scope): "nat" | "int" | "bigint" | "literal" | "boolean" | "string" | "other" {
    if (ts.isParenthesizedExpression(e)) return this.kindOf(e.expression, scope);
    if (ts.isNumericLiteral(e)) return "literal";
    if (ts.isBigIntLiteral(e)) return "bigint";
    const fromTypeNode = (t: ts.TypeNode | undefined): ReturnType<Translator["kindOf"]> => {
      if (t === undefined) return "other";
      if (ts.isIntersectionTypeNode(t)) {
        for (const m of t.types) {
          const k = fromTypeNode(m);
          if (k !== "other") return k;
        }
        return "other";
      }
      if (t.kind === ts.SyntaxKind.BooleanKeyword) return "boolean";
      if (t.kind === ts.SyntaxKind.StringKeyword) return "string";
      if (t.kind === ts.SyntaxKind.BigIntKeyword) return "bigint";
      if (ts.isTypeReferenceNode(t)) {
        const n = this.ps(t.typeName);
        if (n === "nat" || n === "Nat") return "nat";
        if (n === "int" || n === "Int") return "int";
        if (n === undefined) {
          const sym = this.checker.getSymbolAtLocation(t.typeName);
          const d = sym?.declarations?.[0];
          if (d !== undefined && ts.isTypeParameterDeclaration(d)) return fromTypeNode(d.constraint);
        }
      }
      return "other";
    };
    if (ts.isIdentifier(e)) {
      const d = this.declOf(e);
      if (d !== undefined && (ts.isParameter(d) || ts.isVariableDeclaration(d))) return fromTypeNode(d.type ?? undefined) !== "other" ? fromTypeNode(d.type) : d.initializer !== undefined && ts.isVariableDeclaration(d) ? this.kindOf(d.initializer, scope) : "other";
      return "other";
    }
    if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression)) {
      const sym = this.checker.getSymbolAtLocation(e.expression);
      const f = sym === undefined ? undefined : scope.narrowed.get(sym)?.get(e.name.text);
      return f === undefined ? "other" : fromTypeNode(f.type);
    }
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
      const fl = fnLike(this.declOf(e.expression));
      return fl === undefined ? "other" : fromTypeNode(fl.type);
    }
    if (ts.isBinaryExpression(e)) {
      const k = e.operatorToken.kind;
      if (k === ts.SyntaxKind.PlusToken || k === ts.SyntaxKind.AsteriskToken || k === ts.SyntaxKind.MinusToken) {
        const a = this.kindOf(e.left, scope);
        const b = this.kindOf(e.right, scope);
        if (k === ts.SyntaxKind.MinusToken && (a === "nat" || a === "literal")) return "int";
        if (a === "int" || b === "int") return "int";
        if (a === "bigint" || b === "bigint") return "bigint";
        if ((a === "nat" || a === "literal") && (b === "nat" || b === "literal")) return a === "literal" && b === "literal" ? "literal" : "nat";
        return "other";
      }
      return "boolean";
    }
    if (this.isBooleanType(e)) return "boolean";
    return "other";
  }

  /** `===` must have the same meaning in JavaScript and in the logic: primitives only. */
  requireEqualityType(e: ts.BinaryExpression): void {
    const t = this.checker.getBaseTypeOfLiteralType(this.checker.getTypeAtLocation(e.left));
    if (!(t.flags & (ts.TypeFlags.NumberLike | ts.TypeFlags.BooleanLike | ts.TypeFlags.StringLike | ts.TypeFlags.BigIntLike))) {
      this.fail(e, "`===` on objects compares identity in JavaScript; use `eq(a, b)` for structural equality in statements");
    }
  }

  /** Arithmetic is supported on `nat`/`int`/`bigint`, whose logical meaning is exact integers. */
  requireIntegerType(e: ts.BinaryExpression, scope: Scope): void {
    for (const side of [e.left, e.right]) {
      const k = this.kindOf(side, scope);
      if (k !== "nat" && k !== "int" && k !== "bigint" && k !== "literal") {
        this.fail(side, "arithmetic in the logic needs `nat`, `int` or `bigint` operands (`number` is IEEE-754 floating point)");
      }
    }
  }

  objectLiteral(e: ts.ObjectLiteralExpression, scope: Scope, deps: Set<string>): string {
    const ctx = this.checker.getContextualType(e);
    const shape = ctx === undefined ? undefined : this.shapeOfType(ctx);
    if (shape === undefined) return this.fail(e, "object literals are only supported as constructors of inductive types");
    deps.add(shape.leanName);
    const props = new Map<string, ts.Expression>();
    for (const p of e.properties) {
      if (!ts.isPropertyAssignment(p) || !ts.isIdentifier(p.name)) return this.fail(p, "unsupported property");
      props.set(p.name.text, p.initializer);
    }
    const tagExpr = props.get("tag");
    if (tagExpr === undefined || !ts.isStringLiteral(tagExpr)) return this.fail(e, "constructor literal needs a `tag`");
    const ctor = shape.ctors.find((c) => c.tag === tagExpr.text);
    if (ctor === undefined) return this.fail(tagExpr, `unknown constructor "${tagExpr.text}"`);
    const args = ctor.fields.map((f) => {
      const v = props.get(f.name);
      if (v === undefined) return this.fail(e, `missing field ${f.name}`);
      return this.expr(v, "value", scope, deps);
    });
    return `(${shape.leanName}.${this.ident(ctor.tag)}${args.map((a) => ` ${a}`).join("")})`;
  }

  call(e: ts.CallExpression, mode: Mode, scope: Scope, deps: Set<string>): string {
    const ps = this.ps(e.expression);
    const args = e.arguments;
    if (ps !== undefined) {
      switch (ps) {
        case "implies":
          return mode === "prop"
            ? `(∀ (_ : ${this.expr(args[0]!, "prop", scope, deps)}), ${this.expr(args[1]!, "prop", scope, deps)})`
            : `(!${this.expr(args[0]!, "value", scope, deps)} || ${this.expr(args[1]!, "value", scope, deps)})`;
        case "iff":
          return mode === "prop"
            ? `(${this.expr(args[0]!, "prop", scope, deps)} ↔ ${this.expr(args[1]!, "prop", scope, deps)})`
            : `(${this.expr(args[0]!, "value", scope, deps)} == ${this.expr(args[1]!, "value", scope, deps)})`;
        case "eq":
          if (mode !== "prop") return this.fail(e, "`eq` is a proposition, not a boolean");
          return `(${this.expr(args[0]!, "value", scope, deps)} = ${this.expr(args[1]!, "value", scope, deps)})`;
        case "forall":
        case "exists": {
          if (mode !== "prop") return this.fail(e, `\`${ps}\` is a proposition, not a boolean`);
          const f = args[0];
          if (f === undefined || !ts.isArrowFunction(f) || ts.isBlock(f.body)) return this.fail(e, `\`${ps}\` takes an arrow function with an expression body`);
          const locals = new Map(scope.locals);
          const binders: string[] = [];
          const typeParams = new Map<ts.Symbol, string>();
          for (const p of f.parameters) {
            if (!ts.isIdentifier(p.name) || p.type === undefined) return this.fail(p, "quantified variables need a name and a type");
            const n = this.freshVar(p.name.text);
            const sym = this.checker.getSymbolAtLocation(p.name);
            if (sym !== undefined) locals.set(sym, n);
            binders.push(`(${n} : ${this.type(p.type, deps, typeParams)})`);
          }
          const body = this.expr(f.body as ts.Expression, "prop", { locals, narrowed: scope.narrowed }, deps);
          return `(${ps === "forall" ? "∀" : "∃"} ${binders.join(" ")}, ${body})`;
        }
        default:
          return this.fail(e, `ProofScript's ${ps} cannot be used here`);
      }
    }
    if (!ts.isIdentifier(e.expression)) return this.fail(e.expression, "only calls to named functions are supported in the logic yet");
    const decl = this.declOf(e.expression);
    if (decl === undefined || fnLike(decl) === undefined) return this.fail(e.expression, "only calls to functions declared in your project are supported in the logic yet");
    if (!this.isUserDecl(decl)) return this.fail(e.expression, "this function is not part of the logic (only functions in your project can be reflected)");
    const ln = this.requireDecl(decl);
    deps.add(ln);
    const r = `(${ln}${args.map((a) => ` ${this.expr(a, "value", scope, deps)}`).join("")})`;
    return this.coerceProp(e, r, mode);
  }

  // ---- Theorems --------------------------------------------------------------------------------

  translateTheorem(fn: ts.FunctionDeclaration): GeneratedDecl {
    const leanName = this.leanNameOf(fn);
    const deps = new Set<string>();
    const scope: Scope = { locals: new Map(), narrowed: new Map() };
    const typeParams = new Map<ts.Symbol, string>();
    const binders = this.typeParamBinders(fn.typeParameters, deps, typeParams);
    const savedTypeParams = this.#currentTypeParams;
    this.#currentTypeParams = typeParams;
    try {
      return this.#theoremBody(fn, leanName, deps, scope, typeParams, binders);
    } finally {
      this.#currentTypeParams = savedTypeParams;
    }
  }

  #theoremBody(
    fn: ts.FunctionDeclaration,
    leanName: string,
    deps: Set<string>,
    scope: Scope,
    typeParams: Map<ts.Symbol, string>,
    binders: string[],
  ): GeneratedDecl {
    for (const p of fn.parameters) {
      if (!ts.isIdentifier(p.name) || p.type === undefined) return this.fail(p, "theorem parameters need a name and a type");
      const n = this.ident(p.name.text);
      const sym = this.checker.getSymbolAtLocation(p.name);
      if (sym !== undefined) scope.locals.set(sym, n);
      binders.push(`(${n} : ${this.type(p.type, deps, typeParams)})`);
    }
    const ret = this.singleReturn(fn);
    if (ret === undefined) return this.fail(fn, "a theorem's body must be a single `return` statement");
    let statement: string;
    let proofNode: ts.Expression;
    if (ts.isCallExpression(ret) && this.ps(ret.expression) === "prove") {
      const [stmt, proof] = ret.arguments;
      if (stmt === undefined || proof === undefined) return this.fail(ret, "`prove` takes a statement and a proof");
      statement = this.expr(stmt, "prop", scope, deps);
      proofNode = proof;
    } else {
      statement = this.type(fn.type!, deps, typeParams);
      proofNode = ret;
    }
    const attrs = fn.type !== undefined && this.hasSimpAttribute(fn.type) ? "@[simp] " : "";
    const proof = this.proof(proofNode, scope, deps);
    deps.delete(leanName);
    const source = `${attrs}theorem ${leanName}${binders.map((b) => ` ${b}`).join("")} :\n    ${statement} :=\n  ${indent(proof, 2)}`;
    return { kind: "theorem", tsName: fn.name!.text, leanName, node: fn, source, deps };
  }

  hasSimpAttribute(t: ts.TypeNode): boolean {
    if (ts.isIntersectionTypeNode(t)) return t.types.some((x) => this.hasSimpAttribute(x));
    return ts.isTypeReferenceNode(t) && this.ps(t.typeName) === "Simp";
  }

  /** A proof: a tactic script (`by(…)` or a single tactic) or a term (`() => …`). */
  proof(e: ts.Expression, scope: Scope, deps: Set<string>): string {
    if (ts.isArrowFunction(e) && e.parameters.length === 0 && !ts.isBlock(e.body)) return this.term(e.body as ts.Expression, scope, deps);
    return `by\n  ${indent(this.tactic(e, scope, deps), 2)}`;
  }

  tactic(e: ts.Expression, scope: Scope, deps: Set<string>): string {
    if (ts.isIdentifier(e)) {
      const ps = this.ps(e);
      if (ps === "omega" || ps === "rfl" || ps === "decide" || ps === "trivial" || ps === "simp_all" || ps === "sorry" || ps === "grind" || ps === "constructor") return ps;
      return this.fail(e, `\`${e.text}\` is not a tactic`);
    }
    if (!ts.isCallExpression(e)) return this.fail(e, "expected a tactic");
    const ps = this.ps(e.expression);
    const args = e.arguments;
    switch (ps) {
      case "by":
        return args.map((a) => this.tactic(a, scope, deps)).join("\n");
      case "simp":
      case "simp_all": {
        const lemmas = args.map((a) => this.lemmaRef(a, scope, deps));
        return lemmas.length === 0 ? ps : `${ps} [${lemmas.join(", ")}]`;
      }
      case "exact":
        return `exact ${this.term(args[0]!, scope, deps)}`;
      case "apply":
        return `apply ${this.term(args[0]!, scope, deps)}`;
      case "unfold":
        return `unfold ${args.map((a) => this.lemmaRef(a, scope, deps)).join(" ")}`;
      case "rw":
        return `rw [${args.map((a) => this.lemmaRef(a, scope, deps)).join(", ")}]`;
      case "allGoals":
        return `all_goals (${this.tactic(args[0]!, scope, deps).replace(/\n/g, "; ")})`;
      case "intro":
        return `intro ${args.map((a) => (ts.isStringLiteral(a) ? this.ident(a.text) : this.fail(a, "intro takes names"))).join(" ")}`;
      case "induction":
      case "cases": {
        const target = args[0];
        if (target === undefined || !ts.isIdentifier(target)) return this.fail(e, `${ps} takes a variable`);
        const x = this.local(target, scope);
        const casesObj = args[1];
        if (casesObj === undefined) return `${ps} ${x}`;
        if (!ts.isObjectLiteralExpression(casesObj)) return this.fail(casesObj, "cases must be an object of callbacks");
        const lines = [`${ps} ${x} with`];
        for (const p of casesObj.properties) {
          if (!ts.isPropertyAssignment(p) || !ts.isIdentifier(p.name) || !ts.isArrowFunction(p.initializer)) {
            return this.fail(p, "each case is `name: (fields…) => tactic`");
          }
          const f = p.initializer;
          const locals = new Map(scope.locals);
          const names = f.parameters.map((q) => {
            if (!ts.isIdentifier(q.name)) return this.fail(q, "case parameters must be names");
            const n = this.freshVar(q.name.text.replace(/^_+/, "") || "h");
            const sym = this.checker.getSymbolAtLocation(q.name);
            if (sym !== undefined) locals.set(sym, n);
            return n;
          });
          if (ts.isBlock(f.body)) return this.fail(f.body, "case bodies must be tactic expressions");
          const body = this.tactic(f.body, { locals, narrowed: scope.narrowed }, deps);
          lines.push(`| ${this.ident(p.name.text)}${names.map((n) => ` ${n}`).join("")} =>\n  ${indent(body, 2)}`);
        }
        return lines.join("\n");
      }
      default:
        return this.fail(e, "unknown tactic");
    }
  }

  /** A lemma or definition name in `simp […]` / `rw […]`. */
  lemmaRef(e: ts.Expression, scope: Scope, deps: Set<string>): string {
    if (ts.isIdentifier(e)) {
      const sym = this.checker.getSymbolAtLocation(e);
      const l = sym === undefined ? undefined : scope.locals.get(sym);
      if (l !== undefined) return l;
      const decl = this.declOf(e);
      if (decl !== undefined && fnLike(decl) !== undefined) {
        const ln = this.requireDecl(decl);
        deps.add(ln);
        return ln;
      }
    }
    return this.fail(e, "expected the name of a function, theorem or hypothesis");
  }

  /** `I.ctor` where `I` is an inductive proposition: the Lean constructor name. */
  propConstructor(e: ts.PropertyAccessExpression, deps: Set<string>): string | undefined {
    const decl = this.declOf(e.expression);
    if (decl === undefined) return undefined;
    const sym = this.checker.getSymbolAtLocation(e.expression);
    const iface = sym?.declarations?.find((d): d is ts.InterfaceDeclaration => ts.isInterfaceDeclaration(d));
    if (iface === undefined || !this.extendsProp(iface)) return undefined;
    const ln = this.requireDecl(iface);
    deps.add(ln);
    return `${ln}.${this.ident(e.name.text)}`;
  }

  /** Proof terms. */
  term(e: ts.Expression, scope: Scope, deps: Set<string>): string {
    if (ts.isParenthesizedExpression(e)) return `(${this.term(e.expression, scope, deps)})`;
    if (ts.isIdentifier(e)) {
      const ps = this.ps(e);
      if (ps === "rfl") return "rfl";
      if (ps === "sorry") return "sorry";
      return this.expr(e, "value", scope, deps);
    }
    if (ts.isConditionalExpression(e)) {
      return this.branch(e.condition, (s) => this.term(e.whenTrue, s, deps), (s) => this.term(e.whenFalse, s, deps), scope, deps);
    }
    if (ts.isArrowFunction(e)) {
      const locals = new Map(scope.locals);
      const binders: string[] = [];
      for (const p of e.parameters) {
        if (!ts.isIdentifier(p.name) || p.type === undefined) return this.fail(p, "parameters need a name and a type");
        const n = this.freshVar(p.name.text);
        const sym = this.checker.getSymbolAtLocation(p.name);
        if (sym !== undefined) locals.set(sym, n);
        binders.push(`(${n} : ${this.type(p.type, deps, new Map())})`);
      }
      if (ts.isBlock(e.body)) return this.fail(e.body, "use an expression body");
      return `(fun ${binders.join(" ")} => ${this.expr(e.body, "value", { locals, narrowed: scope.narrowed }, deps)})`;
    }
    if (ts.isCallExpression(e)) {
      const ps = this.ps(e.expression);
      if (ps === "congrArg") return `(congrArg ${this.term(e.arguments[0]!, scope, deps)} ${this.term(e.arguments[1]!, scope, deps)})`;
      if (ps !== undefined) return this.fail(e, `ProofScript's ${ps} is not a proof term`);
      if (ts.isPropertyAccessExpression(e.expression) && ts.isIdentifier(e.expression.expression)) {
        const ctor = this.propConstructor(e.expression, deps);
        if (ctor !== undefined) return `(${ctor}${e.arguments.map((a) => ` ${this.term(a, scope, deps)}`).join("")})`;
      }
      if (ts.isIdentifier(e.expression)) {
        const decl = this.declOf(e.expression);
        if (decl !== undefined && fnLike(decl) !== undefined) {
          const ln = this.requireDecl(decl);
          deps.add(ln);
          return `(${ln}${e.arguments.map((a) => ` ${this.term(a, scope, deps)}`).join("")})`;
        }
      }
    }
    return this.expr(e, "value", scope, deps);
  }
}

/** Whether a binder name belongs to an implicit `{T : Type}`/`{n : Nat}` binder (not passed explicitly). */
function b0IsType(name: string, binders: readonly string[]): boolean {
  return binders.some((b) => b.startsWith(`{${name} :`));
}

function blockStatements(s: ts.Statement): readonly ts.Statement[] {
  return ts.isBlock(s) ? s.statements : [s];
}

function endsInReturn(s: ts.Statement): boolean {
  if (ts.isReturnStatement(s)) return true;
  if (ts.isBlock(s)) {
    const last = s.statements[s.statements.length - 1];
    return last !== undefined && endsInReturn(last);
  }
  if (ts.isIfStatement(s)) return s.elseStatement !== undefined && endsInReturn(s.thenStatement) && endsInReturn(s.elseStatement);
  return false;
}

function indent(s: string, n: number): string {
  return s.replace(/\n/g, `\n${" ".repeat(n)}`);
}
