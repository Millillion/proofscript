// Loading a TypeScript project and recognizing ProofScript's symbols.

import { existsSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import ts from "typescript6";

export interface Project {
  readonly program: ts.Program;
  readonly checker: ts.TypeChecker;
  readonly rootDir: string;
}

export function loadProject(tsconfigOrFiles: string | readonly string[]): Project {
  if (typeof tsconfigOrFiles === "string") {
    const configPath = resolve(tsconfigOrFiles);
    const read = ts.readConfigFile(configPath, ts.sys.readFile);
    if (read.error) throw new Error(ts.flattenDiagnosticMessageText(read.error.messageText, "\n"));
    const parsed = ts.parseJsonConfigFileContent(read.config, ts.sys, dirname(configPath));
    const program = ts.createProgram(parsed.fileNames, parsed.options);
    return { program, checker: program.getTypeChecker(), rootDir: dirname(configPath) };
  }
  const options: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    strict: true,
    allowImportingTsExtensions: true,
    noEmit: true,
  };
  const program = ts.createProgram(tsconfigOrFiles.map((f) => resolve(f)), options);
  return { program, checker: program.getTypeChecker(), rootDir: dirname(resolve(tsconfigOrFiles[0]!)) };
}

const packageNameCache = new Map<string, string | undefined>();

/** The `name` of the nearest package.json above `file`. */
function packageNameOf(file: string): string | undefined {
  let dir = dirname(file);
  for (;;) {
    if (packageNameCache.has(dir)) return packageNameCache.get(dir);
    const pj = join(dir, "package.json");
    if (existsSync(pj)) {
      let n: string | undefined;
      try {
        n = (JSON.parse(readFileSync(pj, "utf8")) as { name?: string }).name;
      } catch {
        n = undefined;
      }
      packageNameCache.set(dir, n);
      return n;
    }
    const up = dirname(dir);
    if (up === dir) return undefined;
    dir = up;
  }
}

/**
 * If `symbol` (after following aliases) is declared by the `proofscript`
 * package, returns its exported name. ProofScript recognizes its constructs
 * by symbol, never by spelling, so user declarations named `prove` or `nat`
 * are never misread.
 */
export function proofscriptName(project: Project, symbol: ts.Symbol | undefined): string | undefined {
  if (symbol === undefined) return undefined;
  let s = symbol;
  if (s.flags & ts.SymbolFlags.Alias) s = project.checker.getAliasedSymbol(s);
  const decl = s.declarations?.[0];
  if (decl === undefined) return undefined;
  const file = decl.getSourceFile().fileName;
  if (packageNameOf(file) !== "proofscript") return undefined;
  return s.getName();
}
