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
}

type Mode = "value" | "prop";

interface Scope {
  /** Lean spelling for local symbols (parameters, callback parameters, `const`s, narrowed fields). */
  readonly locals: Map<ts.Symbol, string>;
  /** For variables narrowed to a constructor: field name -> Lean variable. */
  readonly narrowed: Map<ts.Symbol, Map<string, string>>;
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
  readonly #inductives = new Map<ts.Node, InductiveShape>();
  readonly #inProgress = new Set<ts.Node>();
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
        if (ts.isFunctionDeclaration(st) && st.name !== undefined && this.isTheorem(st)) {
          this.#guard(st, () => this.requireDecl(st));
        }
      }
    }
    return { decls: this.ordered(), diagnostics: this.diagnostics };
  }

  #guard(node: ts.Node, f: () => void): void {
    try {
      f();
    } catch (e) {
      if (e instanceof TranslationError) this.diagnostics.push(this.diag(e.node, e.message));
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
        const g = this.isTheorem(decl) ? this.translateTheorem(decl) : this.translateFunction(decl);
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
  type(t: ts.TypeNode, deps: Set<string>, typeParams: Map<ts.Symbol, string>): string {
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
      const decl = this.declOf(t.typeName);
      if (decl !== undefined && (ts.isTypeAliasDeclaration(decl) || ts.isInterfaceDeclaration(decl))) {
        const ln = this.requireDecl(decl);
        deps.add(ln);
        return args.length === 0 ? ln : `(${ln} ${args.join(" ")})`;
      }
    }
    if (ts.isTypeQueryNode(t)) {
      // `typeof x` in an index position: the value x itself.
      return this.fail(t, "`typeof x` value indices are not supported by the Lean engine yet");
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
    return shape;
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

  translateFunction(fn: ts.FunctionDeclaration): GeneratedDecl {
    const leanName = this.leanNameOf(fn);
    if (fn.body === undefined) return this.fail(fn, "functions used in the logic need a body");
    if (fn.type === undefined) return this.fail(fn, "functions used in the logic need a declared return type");
    if (fn.asteriskToken !== undefined || fn.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
      return this.fail(fn, "generators and async functions cannot be used in the logic");
    }
    const deps = new Set<string>();
    const scope: Scope = { locals: new Map(), narrowed: new Map() };
    const typeParams = new Map<ts.Symbol, string>();
    const binders = this.typeParamBinders(fn.typeParameters, deps, typeParams);
    for (const p of fn.parameters) {
      if (!ts.isIdentifier(p.name) || p.type === undefined || p.initializer !== undefined || p.dotDotDotToken !== undefined) {
        return this.fail(p, "parameters of functions used in the logic need a plain name and a type");
      }
      const n = this.ident(p.name.text);
      const sym = this.checker.getSymbolAtLocation(p.name);
      if (sym !== undefined) scope.locals.set(sym, n);
      binders.push(`(${n} : ${this.type(p.type, deps, typeParams)})`);
    }
    const ret = this.type(fn.type, deps, typeParams);
    const body = this.statements(fn.body.statements, 0, scope, deps, fn);
    deps.delete(leanName);
    const source = `def ${leanName}${binders.map((b) => ` ${b}`).join("")} : ${ret} :=\n  ${indent(body, 2)}`;
    return { kind: "def", tsName: fn.name!.text, leanName, node: fn, source, deps };
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
      const fields = new Map<string, string>();
      const vars = c.fields.map((f) => {
        const v = this.freshVar(f.name);
        fields.set(f.name, v);
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
    const c = this.expr(cond, "value", scope, deps);
    return `if ${c} then\n  ${indent(a(scope), 2)}\nelse\n  ${indent(b(scope), 2)}`;
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
      if (decl !== undefined && ts.isFunctionDeclaration(decl)) {
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
          return this.coerceProp(e, f, mode);
        }
        if (e.name.text !== "tag" && this.shapeOfType(this.checker.getTypeAtLocation(e.expression)) !== undefined) {
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
        this.requireIntegerType(e);
        const op = k === ts.SyntaxKind.PlusToken ? "+" : k === ts.SyntaxKind.AsteriskToken ? "*" : "-";
        if (op === "-" && this.isNatExpr(e.left)) {
          return this.fail(e, "subtraction on `nat` is not supported in the logic yet (its result may be negative in JavaScript)");
        }
        return `(${sub(e.left, "value")} ${op} ${sub(e.right, "value")})`;
      }
      default:
        return this.fail(e.operatorToken, `operator ${e.operatorToken.getText()} is not supported in the logic yet`);
    }
  }

  isNatExpr(e: ts.Expression): boolean {
    const t = this.checker.getTypeAtLocation(e);
    const alias = t.aliasSymbol;
    return alias !== undefined && proofscriptName(this.project, alias) === "nat";
  }

  /** `===` must have the same meaning in JavaScript and in the logic: primitives only. */
  requireEqualityType(e: ts.BinaryExpression): void {
    const t = this.checker.getTypeAtLocation(e.left);
    if (!(t.flags & (ts.TypeFlags.NumberLike | ts.TypeFlags.BooleanLike | ts.TypeFlags.StringLike | ts.TypeFlags.BigIntLike))) {
      this.fail(e, "`===` on objects compares identity in JavaScript; use `eq(a, b)` for structural equality in statements");
    }
  }

  /** Arithmetic is supported on `nat`/`int`/`bigint`, whose logical meaning is exact integers. */
  requireIntegerType(e: ts.BinaryExpression): void {
    for (const side of [e.left, e.right]) {
      const t = this.checker.getTypeAtLocation(side);
      const alias = t.aliasSymbol === undefined ? undefined : proofscriptName(this.project, t.aliasSymbol);
      const ok = alias === "nat" || alias === "int" || alias === "Nat" || alias === "Int" || (t.flags & ts.TypeFlags.BigIntLike) !== 0 || ts.isNumericLiteral(side);
      if (!ok) this.fail(side, "arithmetic in the logic needs `nat`, `int` or `bigint` operands (`number` is IEEE-754 floating point)");
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
            ? `(${this.expr(args[0]!, "prop", scope, deps)} → ${this.expr(args[1]!, "prop", scope, deps)})`
            : `(!${this.expr(args[0]!, "value", scope, deps)} || ${this.expr(args[1]!, "value", scope, deps)})`;
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
    if (decl === undefined || !ts.isFunctionDeclaration(decl)) return this.fail(e.expression, "only calls to function declarations are supported in the logic yet");
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
      if (decl !== undefined && ts.isFunctionDeclaration(decl)) {
        const ln = this.requireDecl(decl);
        deps.add(ln);
        return ln;
      }
    }
    return this.fail(e, "expected the name of a function, theorem or hypothesis");
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
      if (ts.isIdentifier(e.expression)) {
        const decl = this.declOf(e.expression);
        if (decl !== undefined && ts.isFunctionDeclaration(decl)) {
          const ln = this.requireDecl(decl);
          deps.add(ln);
          return `(${ln}${e.arguments.map((a) => ` ${this.term(a, scope, deps)}`).join("")})`;
        }
      }
    }
    return this.expr(e, "value", scope, deps);
  }
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
