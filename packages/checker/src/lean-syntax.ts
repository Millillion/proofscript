// A parser for the Lean source ProofScript's translator generates.
//
// Certificates (certificate.ts) are checked without Lean: the statements of theorems, the
// signatures and equations of definitions, and the constructors of inductive types are
// elaborated by ProofScript itself (elab.ts) from this syntax. Proofs are never parsed: a
// `by` block is skipped, since only its existence matters (the kernel checks the proof term).
//
// The grammar is the subset the translator emits, not all of Lean. Anything outside it is a
// parse error, and the declaration is then not bound (it needs Lean), never misread.

export type Term =
  | { readonly k: "ident"; readonly name: string }
  | { readonly k: "dot"; readonly name: string }
  | { readonly k: "num"; readonly value: bigint }
  | { readonly k: "app"; readonly fn: Term; readonly args: readonly Term[] }
  | { readonly k: "binop"; readonly op: string; readonly l: Term; readonly r: Term }
  | { readonly k: "unop"; readonly op: "¬" | "!" | "-"; readonly e: Term }
  | { readonly k: "field"; readonly e: Term; readonly name: string }
  | { readonly k: "index"; readonly e: Term; readonly i: Term }
  | { readonly k: "arrayLit"; readonly elems: readonly Term[] }
  | { readonly k: "listLit"; readonly elems: readonly Term[] }
  | { readonly k: "tuple"; readonly elems: readonly Term[] }
  | { readonly k: "unit" }
  | { readonly k: "ascribe"; readonly e: Term; readonly type: Term }
  | { readonly k: "forall" | "exists" | "fun"; readonly binders: readonly Binder[]; readonly body: Term }
  | { readonly k: "if"; readonly h: string | undefined; readonly cond: Term; readonly then: Term; readonly else: Term }
  | { readonly k: "match"; readonly discr: Term; readonly alts: readonly MatchAlt[] }
  | { readonly k: "let"; readonly names: readonly string[]; readonly type: Term | undefined; readonly value: Term; readonly body: Term }
  | { readonly k: "have"; readonly name: string; readonly type: Term | undefined; readonly value: Term | undefined; readonly body: Term }
  | { readonly k: "by" }
  | { readonly k: "sort"; readonly which: "Type" | "Prop" };

export interface Binder {
  readonly name: string;
  readonly type: Term | undefined;
  readonly implicit: boolean;
  /** Had a default `:= by …` (an autoParam). */
  readonly auto: boolean;
}

export interface MatchAlt {
  /** Constructor name, or `_` for a wildcard. */
  readonly ctor: string;
  readonly vars: readonly string[];
  /** `.ctor ..`: fields ignored. */
  readonly ellipsis: boolean;
  readonly body: Term;
}

export type Decl =
  | { readonly k: "theorem"; readonly name: string; readonly binders: readonly Binder[]; readonly type: Term }
  | { readonly k: "def"; readonly name: string; readonly binders: readonly Binder[]; readonly type: Term; readonly body: Term }
  | {
      readonly k: "inductive";
      readonly name: string;
      readonly binders: readonly Binder[];
      readonly type: Term | undefined;
      readonly ctors: readonly { readonly name: string; readonly binders: readonly Binder[]; readonly type: Term }[];
    };

export class ParseError extends Error {
  override readonly name = "ParseError";
}

interface Token {
  readonly kind: "id" | "num" | "sym" | "eof";
  readonly v: string;
  /** Whitespace (of any kind) directly before this token. */
  readonly sp: boolean;
  /** A line break before this token. */
  readonly nl: boolean;
}

const SYMBOLS = [
  ":=", "=>", "++", "==", "!=", "&&", "||", "..", "#[", "@[",
  "(", ")", "[", "]", "{", "}", ",", ":", "|", "'", ";", "+", "-", "*", "/", "%", "<", ">", "=", "!", "_",
  "≤", "≥", "≠", "∧", "∨", "¬", "↔", "→", "×", "∀", "∃", "λ", ".",
];
const KEYWORDS = new Set(["fun", "let", "have", "if", "then", "else", "match", "with", "by", "theorem", "def", "inductive", "where", "termination_by", "set_option", "in"]);

const isIdStart = (c: string) => /[A-Za-z_α-ωΑ-Ω]/.test(c) && c !== "λ";
const isIdChar = (c: string) => /[A-Za-z0-9_'!?α-ωΑ-Ω₀-₉]/.test(c) && c !== "λ";

export function tokenize(src: string): Token[] {
  const out: Token[] = [];
  let i = 0;
  let sp = false;
  let nl = false;
  while (i < src.length) {
    const c = src[i]!;
    if (c === "\n") {
      sp = nl = true;
      i++;
      continue;
    }
    if (c === " " || c === "\t" || c === "\r") {
      sp = true;
      i++;
      continue;
    }
    if (c === "-" && src[i + 1] === "-") {
      while (i < src.length && src[i] !== "\n") i++;
      continue;
    }
    if (/[0-9]/.test(c)) {
      let j = i;
      while (j < src.length && /[0-9]/.test(src[j]!)) j++;
      out.push({ kind: "num", v: src.slice(i, j), sp, nl });
      i = j;
    } else if (isIdStart(c) && !(c === "_" && !isIdChar(src[i + 1] ?? " "))) {
      // Identifiers include dotted parts (`PS.m.f`, `out_9.push`, `p.2`); `'` only inside.
      let j = i;
      for (;;) {
        while (j < src.length && isIdChar(src[j]!) && src[j] !== "'") j++;
        if (src[j] === "." && j + 1 < src.length && (isIdStart(src[j + 1]!) || /[0-9]/.test(src[j + 1]!))) {
          j++;
          continue;
        }
        break;
      }
      out.push({ kind: "id", v: src.slice(i, j), sp, nl });
      i = j;
    } else {
      const s = SYMBOLS.find((x) => src.startsWith(x, i));
      if (s === undefined) throw new ParseError(`unexpected character ${JSON.stringify(c)}`);
      out.push({ kind: "sym", v: s, sp, nl });
      i += s.length;
    }
    sp = nl = false;
  }
  out.push({ kind: "eof", v: "", sp: true, nl: true });
  return out;
}

/** Binary operators: precedence, and whether they associate to the right. */
const BINOPS: Record<string, [number, boolean]> = {
  "↔": [20, false],
  "→": [25, true],
  "∨": [30, true],
  "||": [30, false],
  "∧": [35, true],
  "&&": [35, false],
  "×": [35, true],
  "=": [50, false],
  "≠": [50, false],
  "<": [50, false],
  "≤": [50, false],
  ">": [50, false],
  "≥": [50, false],
  "==": [50, false],
  "!=": [50, false],
  "++": [65, true],
  "+": [65, false],
  "-": [65, false],
  "*": [70, false],
  "/": [70, false],
  "%": [70, false],
};

class Parser {
  #toks: Token[];
  #i = 0;

  constructor(src: string) {
    this.#toks = tokenize(src);
  }

  get peek(): Token {
    return this.#toks[this.#i]!;
  }
  at(v: string, off = 0): boolean {
    const t = this.#toks[this.#i + off]!;
    return (t.kind === "sym" || t.kind === "id") && t.v === v;
  }
  next(): Token {
    return this.#toks[this.#i++]!;
  }
  expect(v: string): void {
    const t = this.next();
    if (t.v !== v) throw new ParseError(`expected \`${v}\`, found \`${t.v || "end of input"}\``);
  }
  ident(): string {
    const t = this.next();
    if (t.kind !== "id" || KEYWORDS.has(t.v)) {
      if (t.kind === "sym" && t.v === "_") return "_";
      throw new ParseError(`expected a name, found \`${t.v}\``);
    }
    return t.v;
  }
  get done(): boolean {
    return this.peek.kind === "eof";
  }

  /** Skips a tactic block: up to the first unmatched closing bracket (or the end). */
  skipTactic(): void {
    let depth = 0;
    for (;;) {
      const t = this.peek;
      if (t.kind === "eof") return;
      if (t.kind === "sym" && (t.v === "(" || t.v === "[" || t.v === "{" || t.v === "#[" || t.v === "@[")) depth++;
      if (t.kind === "sym" && (t.v === ")" || t.v === "]" || t.v === "}")) {
        if (depth === 0) return;
        depth--;
      }
      this.next();
    }
  }

  // ---- Declarations ---------------------------------------------------------------------------

  decl(): Decl {
    // `set_option name value in` before a declaration only changes how Lean works on it.
    while (this.at("set_option")) {
      this.next();
      this.next();
      this.next();
      this.expect("in");
    }
    if (this.at("@[")) {
      this.next();
      this.skipTactic();
      this.expect("]");
    }
    const kw = this.next().v;
    const name = this.ident();
    if (kw === "theorem" || kw === "def") {
      const binders = this.binders();
      this.expect(":");
      const type = this.term();
      this.expect(":=");
      if (kw === "theorem") return { k: "theorem", name, binders, type };
      const body = this.term();
      if (!this.done && !this.at("termination_by")) throw new ParseError(`unexpected \`${this.peek.v}\` after the body of ${name}`);
      return { k: "def", name, binders, type, body };
    }
    if (kw === "inductive") {
      const binders = this.binders();
      let type: Term | undefined;
      if (this.at(":")) {
        this.next();
        type = this.term();
      }
      this.expect("where");
      const ctors: { name: string; binders: Binder[]; type: Term }[] = [];
      while (this.at("|")) {
        this.next();
        const cname = this.ident();
        const cb = this.binders();
        this.expect(":");
        ctors.push({ name: cname, binders: cb, type: this.term() });
      }
      if (!this.done) throw new ParseError(`unexpected \`${this.peek.v}\` in inductive ${name}`);
      return { k: "inductive", name, binders, type, ctors };
    }
    throw new ParseError(`unsupported declaration kind \`${kw}\``);
  }

  binders(): Binder[] {
    const out: Binder[] = [];
    while (this.at("(") || this.at("{")) {
      const implicit = this.next().v === "{";
      const names: string[] = [];
      while (!this.at(":")) names.push(this.ident());
      this.expect(":");
      const type = this.term();
      let auto = false;
      if (this.at(":=")) {
        this.next();
        if (!this.at("by")) throw new ParseError("only tactic defaults (`:= by …`) are supported in binders");
        this.skipTactic();
        auto = true;
      }
      this.expect(implicit ? "}" : ")");
      for (const n of names) out.push({ name: n, type, implicit, auto });
    }
    return out;
  }

  // ---- Terms ----------------------------------------------------------------------------------

  term(minPrec = 0): Term {
    let lhs = this.prefix();
    for (;;) {
      const t = this.peek;
      if (t.kind !== "sym" && t.kind !== "id") break;
      const op = BINOPS[t.v];
      if (op === undefined || t.nl) break;
      const [prec, right] = op;
      if (prec < minPrec) break;
      this.next();
      const rhs = this.term(right ? prec : prec + 1);
      lhs = { k: "binop", op: t.v, l: lhs, r: rhs };
    }
    return lhs;
  }

  prefix(): Term {
    const t = this.peek;
    // A dependent arrow: `(x : A) → B`, `{T : Type} → B`, `(h : P := by tac) → B`.
    if (t.kind === "sym" && (t.v === "(" || t.v === "{")) {
      const save = this.#i;
      try {
        const binders = this.binders();
        if (binders.length > 0 && this.at("→")) {
          this.next();
          return { k: "forall", binders, body: this.term(25) };
        }
      } catch (e) {
        if (!(e instanceof ParseError)) throw e;
      }
      this.#i = save;
    }
    if (t.kind === "sym") {
      switch (t.v) {
        case "¬":
          this.next();
          return { k: "unop", op: "¬", e: this.term(40) };
        case "!":
          this.next();
          return { k: "unop", op: "!", e: this.application() };
        case "-":
          this.next();
          return { k: "unop", op: "-", e: this.term(75) };
        case "∀":
        case "∃": {
          this.next();
          const binders = this.quantBinders();
          this.expect(",");
          return { k: t.v === "∀" ? "forall" : "exists", binders, body: this.term() };
        }
        case "λ":
          return this.fun();
      }
    }
    if (t.kind === "id") {
      switch (t.v) {
        case "fun":
          return this.fun();
        case "if":
          return this.ite();
        case "match":
          return this.match();
        case "let":
          return this.let();
        case "have":
          return this.have();
        case "by":
          this.next();
          this.skipTactic();
          return { k: "by" };
      }
    }
    return this.application();
  }

  quantBinders(): Binder[] {
    if (this.at("(") || this.at("{")) return this.binders();
    const names: string[] = [];
    while (!this.at(",") && !this.at(":")) names.push(this.ident());
    let type: Term | undefined;
    if (this.at(":")) {
      this.next();
      type = this.term();
    }
    return names.map((name) => ({ name, type, implicit: false, auto: false }));
  }

  fun(): Term {
    this.next();
    const binders: Binder[] = [];
    while (!this.at("=>")) {
      if (this.at("(")) binders.push(...this.binders());
      else binders.push({ name: this.ident(), type: undefined, implicit: false, auto: false });
    }
    this.expect("=>");
    return { k: "fun", binders, body: this.term() };
  }

  ite(): Term {
    this.next();
    let h: string | undefined;
    if (this.peek.kind === "id" && this.at(":", 1)) {
      h = this.ident();
      this.next();
    }
    const cond = this.term();
    this.expect("then");
    const thenT = this.term();
    this.expect("else");
    return { k: "if", h, cond, then: thenT, else: this.term() };
  }

  match(): Term {
    this.next();
    const discr = this.term();
    this.expect("with");
    const alts: MatchAlt[] = [];
    while (this.at("|")) {
      this.next();
      let ctor: string;
      if (this.at("_")) {
        this.next();
        ctor = "_";
      } else {
        this.expect(".");
        ctor = this.ident();
      }
      const vars: string[] = [];
      let ellipsis = false;
      while (!this.at("=>")) {
        if (this.at("..")) {
          this.next();
          ellipsis = true;
        } else vars.push(this.ident());
      }
      this.expect("=>");
      alts.push({ ctor, vars, ellipsis, body: this.term() });
    }
    if (alts.length === 0) throw new ParseError("a match needs alternatives");
    return { k: "match", discr, alts };
  }

  /** The rest of a `let`/`have` block: after a line break or `;`. */
  continuation(): Term {
    if (this.at(";")) this.next();
    else if (!this.peek.nl) throw new ParseError(`expected a line break or \`;\`, found \`${this.peek.v}\``);
    return this.term();
  }

  let(): Term {
    this.next();
    let names: string[];
    if (this.at("(")) {
      this.next();
      names = [this.ident()];
      while (this.at(",")) {
        this.next();
        names.push(this.ident());
      }
      this.expect(")");
    } else names = [this.ident()];
    let type: Term | undefined;
    if (this.at(":")) {
      this.next();
      type = this.term();
    }
    this.expect(":=");
    const value = this.term();
    return { k: "let", names, type, value, body: this.continuation() };
  }

  have(): Term {
    this.next();
    const name = this.ident();
    // With a type, the proof is irrelevant; without one, the type is the proof's.
    if (!this.at(":")) {
      this.expect(":=");
      const value = this.term();
      return { k: "have", name, type: undefined, value, body: this.continuation() };
    }
    this.next();
    const type = this.term();
    this.expect(":=");
    this.term(); // the proof
    return { k: "have", name, type, value: undefined, body: this.continuation() };
  }

  /** Can the current token start an argument of an application? */
  startsArg(): boolean {
    const t = this.peek;
    if (t.nl) return false;
    if (t.kind === "num") return true;
    if (t.kind === "id") return !KEYWORDS.has(t.v);
    if (t.kind === "sym") return t.v === "(" || t.v === "#[" || t.v === "[" || (t.v === "." && this.#toks[this.#i + 1]!.kind === "id" && !this.#toks[this.#i + 1]!.sp);
    return false;
  }

  application(): Term {
    const fn = this.postfix();
    const args: Term[] = [];
    while (this.startsArg()) args.push(this.postfix());
    return args.length === 0 ? fn : { k: "app", fn, args };
  }

  postfix(): Term {
    let e = this.atom();
    for (;;) {
      const t = this.peek;
      if (t.sp) break;
      if (t.kind === "sym" && t.v === "." && this.#toks[this.#i + 1]!.kind !== "eof" && !this.#toks[this.#i + 1]!.sp) {
        this.next();
        const f = this.next();
        if (f.kind !== "id" && f.kind !== "num") throw new ParseError(`expected a field name after \`.\``);
        // `.2.1` arrives as one token `2.1`? No: numbers stop at dots, so fields chain.
        for (const part of f.v.split(".")) e = { k: "field", e, name: part };
      } else if (t.kind === "sym" && t.v === "[") {
        this.next();
        const i = this.term();
        this.expect("]");
        if (!this.at("'")) throw new ParseError("array indexing must carry a proof (`a[i]'h`)");
        this.next();
        this.postfixArg(); // the proof
        e = { k: "index", e, i };
      } else break;
    }
    return e;
  }

  /** A single argument-like term (for the proof after `'`). */
  postfixArg(): Term {
    return this.atom();
  }

  atom(): Term {
    const t = this.next();
    if (t.kind === "num") return { k: "num", value: BigInt(t.v) };
    if (t.kind === "id") {
      if (t.v === "Type" || t.v === "Prop") return { k: "sort", which: t.v };
      if (KEYWORDS.has(t.v)) throw new ParseError(`unexpected \`${t.v}\``);
      // `p.2`, `p.2.1`: numeric parts of an identifier are projections.
      const parts = t.v.split(".");
      const firstNum = parts.findIndex((p) => /^[0-9]/.test(p));
      if (firstNum > 0) {
        let e: Term = { k: "ident", name: parts.slice(0, firstNum).join(".") };
        for (const p of parts.slice(firstNum)) e = { k: "field", e, name: p };
        return e;
      }
      return { k: "ident", name: t.v };
    }
    if (t.kind === "sym") {
      switch (t.v) {
        case ".":
          return { k: "dot", name: this.ident() };
        case "#[":
          return { k: "arrayLit", elems: this.list("]") };
        case "[":
          return { k: "listLit", elems: this.list("]") };
        case "(": {
          if (this.at(")")) {
            this.next();
            return { k: "unit" };
          }
          const e = this.term();
          if (this.at(":")) {
            this.next();
            const type = this.term();
            this.expect(")");
            return { k: "ascribe", e, type };
          }
          if (this.at(",")) {
            const elems = [e];
            while (this.at(",")) {
              this.next();
              elems.push(this.term());
            }
            this.expect(")");
            return { k: "tuple", elems };
          }
          this.expect(")");
          return e;
        }
      }
    }
    throw new ParseError(`unexpected \`${t.v || "end of input"}\``);
  }

  list(close: string): Term[] {
    const out: Term[] = [];
    if (this.at(close)) {
      this.next();
      return out;
    }
    out.push(this.term());
    while (this.at(",")) {
      this.next();
      out.push(this.term());
    }
    this.expect(close);
    return out;
  }
}

export function parseDecl(src: string): Decl {
  return new Parser(src).decl();
}

export function parseTerm(src: string): Term {
  const p = new Parser(src);
  const t = p.term();
  if (!p.done) throw new ParseError(`unexpected \`${p.peek.v}\``);
  return t;
}
