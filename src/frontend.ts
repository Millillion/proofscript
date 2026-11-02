import ts from "typescript";

import { hasFiniteDomain } from "./domains.js";
import { collectHelperCallPairs } from "./equivalence.js";
import { analyzeLoopJoinFunction } from "./loop-join.js";
import { analyzeLoopJoinTailFunction } from "./loop-join-tail.js";
import { analyzeLoopWriteFunction } from "./loop-write.js";
import { analyzeRecursiveAdvanceFunction } from "./recursive-advance.js";

interface ContractMetadata {
  name: string;
  isSpec: boolean;
  specification?: string;
  declaration: ts.FunctionDeclaration;
}

interface LoweredSurfaceResult {
  sourceText: string;
  usedAssert: boolean;
}

function lineIndent(line: string): string {
  const match = line.match(/^\s*/u);
  return match?.[0] ?? "";
}

function trimClausePrefix(line: string, prefix: string): string {
  return line.trim().slice(prefix.length).trim();
}

function parseEnsuresSpecification(ensuresExpressions: string[]): string | undefined {
  for (const expression of ensuresExpressions) {
    const match = expression.match(/^result\s*={2,3}\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(([\s\S]*)\)$/u);
    if (match !== null) {
      return match[1];
    }
  }
  return undefined;
}

function parseLoopHelperCall(line: string): string | undefined {
  const trimmed = line.trim();
  if (trimmed.startsWith("proofscriptInvariant(") && trimmed.endsWith(");")) {
    return `invariant ${trimmed.slice("proofscriptInvariant(".length, -2).trim()}`;
  }
  if (trimmed.startsWith("proofscriptDecreases(") && trimmed.endsWith(");")) {
    return `decreases ${trimmed.slice("proofscriptDecreases(".length, -2).trim()}`;
  }
  return undefined;
}

function lowerSurfaceSyntax(sourceText: string): LoweredSurfaceResult {
  const lines = sourceText.split(/\r?\n/u);
  const output: string[] = [];
  let usedAssert = false;
  const usesTypeMarkers = sourceText.includes("ProofScriptSpec<") || sourceText.includes("ProofScriptImpl<");

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const trimmed = line.trim();
    const functionMatch = line.match(/^(\s*)(export\s+)?(spec\s+)?function\b/u);

    if (functionMatch !== null) {
      const indent = functionMatch[1] ?? "";
      const signatureLines = [line.replace(/\bspec\s+function\b/u, "function")];
      let cursor = index + 1;

      while (
        cursor < lines.length &&
        lines[cursor].trim() !== "{" &&
        !lines[cursor].trim().startsWith("requires ") &&
        !lines[cursor].trim().startsWith("ensures ") &&
        !lines[cursor].trim().startsWith("decreases ") &&
        !signatureLines[signatureLines.length - 1].includes("{")
      ) {
        signatureLines.push(lines[cursor]);
        cursor += 1;
      }

      const requiresExpressions: string[] = [];
      const ensuresExpressions: string[] = [];
      const decreasesExpressions: string[] = [];

      while (cursor < lines.length) {
        const contractLine = lines[cursor].trim();
        if (contractLine.startsWith("requires ")) {
          requiresExpressions.push(trimClausePrefix(lines[cursor], "requires"));
          cursor += 1;
          continue;
        }
        if (contractLine.startsWith("ensures ")) {
          ensuresExpressions.push(trimClausePrefix(lines[cursor], "ensures"));
          cursor += 1;
          continue;
        }
        if (contractLine.startsWith("decreases ")) {
          decreasesExpressions.push(trimClausePrefix(lines[cursor], "decreases"));
          cursor += 1;
          continue;
        }
        break;
      }

      const braceLine =
        cursor < lines.length && lines[cursor].trim() === "{"
          ? lines[cursor]
          : signatureLines[signatureLines.length - 1].includes("{")
            ? undefined
            : undefined;

      const specification = parseEnsuresSpecification(ensuresExpressions);
      if (functionMatch[3] !== undefined || specification !== undefined || requiresExpressions.length > 0 || decreasesExpressions.length > 0) {
        output.push(`${indent}/**`);
        if (functionMatch[3] !== undefined) {
          output.push(`${indent} * @psRole spec`);
        }
        if (specification !== undefined) {
          output.push(`${indent} * @psSpec ${specification}`);
        }
        for (const expression of requiresExpressions) {
          output.push(`${indent} * @psRequires ${expression}`);
        }
        for (const expression of ensuresExpressions) {
          output.push(`${indent} * @psEnsures ${expression}`);
        }
        for (const expression of decreasesExpressions) {
          output.push(`${indent} * @psDecreases ${expression}`);
        }
        output.push(`${indent} */`);
      }

      output.push(...signatureLines);
      if (braceLine !== undefined && !signatureLines[signatureLines.length - 1].includes("{")) {
        output.push(braceLine);
        cursor += 1;
      }

      index = cursor - 1;
      continue;
    }

    if (trimmed.startsWith("while ") || trimmed.startsWith("for ")) {
      if (line.includes("{")) {
        const annotations: string[] = [];
        let cursor = index + 1;
        while (cursor < lines.length) {
          const annotation = parseLoopHelperCall(lines[cursor]);
          if (annotation === undefined) {
            break;
          }
          annotations.push(annotation);
          cursor += 1;
        }

        if (annotations.length > 0) {
          output.push(`${lineIndent(line)}/*`);
          for (const annotation of annotations) {
            output.push(`${lineIndent(line)} * @psLoop ${annotation}`);
          }
          output.push(`${lineIndent(line)} */`);
          output.push(line);
          index = cursor - 1;
          continue;
        }
      } else {
        const annotations: string[] = [];
        let cursor = index + 1;
        while (
          cursor < lines.length &&
          (lines[cursor].trim().startsWith("invariant ") || lines[cursor].trim().startsWith("decreases "))
        ) {
          annotations.push(lines[cursor].trim());
          cursor += 1;
        }

        if (annotations.length > 0 && cursor < lines.length && lines[cursor].trim() === "{") {
          output.push(`${lineIndent(line)}/*`);
          for (const annotation of annotations) {
            output.push(`${lineIndent(line)} * @psLoop ${annotation}`);
          }
          output.push(`${lineIndent(line)} */`);
          output.push(line);
          output.push(lines[cursor]);
          index = cursor;
          continue;
        }
      }
    }

    if (trimmed.startsWith("assert ")) {
      const indent = lineIndent(line);
      const expression = trimClausePrefix(line, "assert");
      output.push(`${indent}proofscriptAssert(${expression});`);
      usedAssert = true;
      continue;
    }

    if (trimmed.startsWith("proofscriptAssert(")) {
      usedAssert = true;
      output.push(line);
      continue;
    }

    output.push(line);
  }

  if (usedAssert) {
    output.unshift(
      "function proofscriptAssert(condition: boolean): void {",
      "  if (!condition) {",
      '    throw new Error("ProofScript assertion failed");',
      "  }",
      "}",
      "",
    );
  }

  if (usesTypeMarkers) {
    output.unshift(
      "type ProofScriptSpec<F extends (...args: any[]) => any> = F;",
      "type ProofScriptImpl<F extends (...args: any[]) => any, S extends (...args: any[]) => any> = F;",
      "",
    );
  }

  return {
    sourceText: output.join("\n"),
    usedAssert,
  };
}

function readTagMap(node: ts.Node): Map<string, string[]> {
  const tagMap = new Map<string, string[]>();
  for (const tag of ts.getJSDocTags(node)) {
    const commentText =
      typeof tag.comment === "string"
        ? tag.comment
        : (tag.comment ?? [])
            .map((part) => ("text" in part ? part.text : ""))
            .join("")
            .trim();
    const list = tagMap.get(tag.tagName.getText()) ?? [];
    list.push(commentText);
    tagMap.set(tag.tagName.getText(), list);
  }
  return tagMap;
}

function buildFunctionMap(sourceFile: ts.SourceFile): Map<string, ts.FunctionDeclaration> {
  const functions = new Map<string, ts.FunctionDeclaration>();
  const visit = (node: ts.Node): void => {
    if (ts.isFunctionDeclaration(node) && node.name !== undefined) {
      functions.set(node.name.text, node);
    }
    ts.forEachChild(node, visit);
  };
  visit(sourceFile);
  return functions;
}

function typeQueryTargetName(typeNode: ts.TypeNode | undefined): string | undefined {
  if (typeNode === undefined || !ts.isTypeQueryNode(typeNode)) {
    return undefined;
  }
  return ts.isIdentifier(typeNode.exprName) ? typeNode.exprName.text : undefined;
}

function collectContracts(sourceFile: ts.SourceFile): Map<string, ContractMetadata> {
  const functionMap = buildFunctionMap(sourceFile);
  const contracts = new Map<string, ContractMetadata>();

  for (const [name, declaration] of functionMap.entries()) {
    const tags = readTagMap(declaration);
    const specification =
      tags.get("psSpec")?.[0] ??
      parseEnsuresSpecification(tags.get("psEnsures") ?? tags.get("ensures") ?? []);
    const isSpec = (tags.get("psRole")?.includes("spec") ?? false) || tags.has("spec");
    if (!isSpec && specification === undefined) {
      continue;
    }
    contracts.set(name, {
      name,
      isSpec,
      specification,
      declaration,
    });
  }

  const visitMarkers = (node: ts.Node): void => {
    if (ts.isVariableStatement(node)) {
      for (const declaration of node.declarationList.declarations) {
        if (
          declaration.type === undefined ||
          !ts.isTypeReferenceNode(declaration.type) ||
          !ts.isIdentifier(declaration.type.typeName)
        ) {
          continue;
        }

        const markerName = declaration.type.typeName.text;
        const typeArguments = declaration.type.typeArguments ?? [];

        if (markerName === "ProofScriptSpec" && typeArguments.length === 1) {
          const functionName = typeQueryTargetName(typeArguments[0]);
          const functionDeclaration = functionName === undefined ? undefined : functionMap.get(functionName);
          if (functionName !== undefined && functionDeclaration !== undefined) {
            contracts.set(functionName, {
              name: functionName,
              isSpec: true,
              declaration: functionDeclaration,
            });
          }
          continue;
        }

        if (markerName === "ProofScriptImpl" && typeArguments.length === 2) {
          const implementationName = typeQueryTargetName(typeArguments[0]);
          const specificationName = typeQueryTargetName(typeArguments[1]);
          const functionDeclaration =
            implementationName === undefined ? undefined : functionMap.get(implementationName);
          if (
            implementationName !== undefined &&
            specificationName !== undefined &&
            functionDeclaration !== undefined
          ) {
            contracts.set(implementationName, {
              name: implementationName,
              isSpec: false,
              specification: specificationName,
              declaration: functionDeclaration,
            });
          }
        }
      }
    }
    ts.forEachChild(node, visitMarkers);
  };

  visitMarkers(sourceFile);

  return contracts;
}

function parameterDomainBindings(declaration: ts.FunctionDeclaration): Array<{ name: string; domain: string }> {
  const bindings: Array<{ name: string; domain: string }> = [];
  for (const parameter of declaration.parameters) {
    if (!ts.isIdentifier(parameter.name) || parameter.type === undefined || !ts.isTypeReferenceNode(parameter.type)) {
      return [];
    }
    const typeName = parameter.type.typeName;
    if (!ts.isIdentifier(typeName) || !hasFiniteDomain(typeName.text)) {
      return [];
    }
    bindings.push({ name: parameter.name.text, domain: typeName.text });
  }
  return bindings;
}

function inferProofKind(
  implementation: ts.FunctionDeclaration,
  specification: ts.FunctionDeclaration,
): { kind: string; metadata: Record<string, string> } {
  const finiteDomains = parameterDomainBindings(implementation);
  if (finiteDomains.length === implementation.parameters.length && finiteDomains.length > 0) {
    return {
      kind: "exhaustive",
      metadata: {
        proofDomains: finiteDomains.map((binding) => `${binding.name}:${binding.domain}`).join(", "),
      },
    };
  }

  if (implementation.parameters.length >= 2) {
    const inputParameter = implementation.parameters[0];
    const indexParameter = implementation.parameters[1];
    if (ts.isIdentifier(inputParameter.name) && ts.isIdentifier(indexParameter.name)) {
      try {
        analyzeRecursiveAdvanceFunction(implementation, inputParameter.name.text, indexParameter.name.text);
        analyzeRecursiveAdvanceFunction(specification, inputParameter.name.text, indexParameter.name.text);
        return {
          kind: "recursiveAdvance",
          metadata: {
            proofInput: inputParameter.name.text,
            proofIndex: indexParameter.name.text,
          },
        };
      } catch {
        // Continue to more general rules.
      }
    }
  }

  try {
    analyzeLoopWriteFunction(implementation);
    analyzeLoopWriteFunction(specification);
    return { kind: "loopWrite", metadata: {} };
  } catch {
    // Continue.
  }

  try {
    analyzeLoopJoinTailFunction(implementation);
    analyzeLoopJoinTailFunction(specification);
    return { kind: "loopJoinTail", metadata: {} };
  } catch {
    // Continue.
  }

  try {
    analyzeLoopJoinFunction(implementation);
    analyzeLoopJoinFunction(specification);
    return { kind: "loopJoin", metadata: {} };
  } catch {
    // Continue.
  }

  return { kind: "composition", metadata: {} };
}

function inferDependencies(
  implementation: ts.FunctionDeclaration,
  specification: ts.FunctionDeclaration,
  theoremNameByImplementation: Map<string, string>,
  contractByImplementation: Map<string, ContractMetadata>,
): string[] {
  const implementationName = implementation.name?.text;
  const specificationName = specification.name?.text;
  const dependencies = new Set<string>();

  for (const pair of collectHelperCallPairs(implementation, specification)) {
    if (pair.implementation === implementationName && pair.specification === specificationName) {
      continue;
    }
    const contract = contractByImplementation.get(pair.implementation);
    if (contract?.specification !== pair.specification) {
      continue;
    }
    const theoremName = theoremNameByImplementation.get(pair.implementation);
    if (theoremName !== undefined) {
      dependencies.add(theoremName);
    }
  }

  return [...dependencies];
}

function renderExhaustiveTheoremBody(
  implementation: ts.FunctionDeclaration,
  specificationName: string,
): string {
  const parameterList = implementation.parameters.map((parameter) => parameter.getText()).join(", ");
  const argumentList = implementation.parameters
    .map((parameter) => {
      if (!ts.isIdentifier(parameter.name)) {
        throw new Error("ProofScript only supports identifier parameters in generated exhaustive theorems");
      }
      return parameter.name.text;
    })
    .join(", ");
  const implementationName = implementation.name?.text;
  if (implementationName === undefined) {
    throw new Error("ProofScript exhaustive theorem generation requires a named function");
  }

  return `export function ${implementationName}MatchesSpec(${parameterList}): boolean {\n  return __proofscriptEqual(${implementationName}(${argumentList}), ${specificationName}(${argumentList}));\n}`;
}

function theoremCommentLines(
  theoremName: string,
  implementationName: string,
  specificationName: string,
  kind: string,
  dependencies: string[],
  metadata: Record<string, string>,
): string[] {
  const lines = ["/**", ` * @proofKind ${kind}`, ` * @proofImplementation ${implementationName}`, ` * @proofSpecification ${specificationName}`];
  if (dependencies.length > 0) {
    lines.push(` * @proofDependencies ${dependencies.join(", ")}`);
  }
  for (const [key, value] of Object.entries(metadata)) {
    lines.push(` * @${key} ${value}`);
  }
  lines.push(" */");
  return lines;
}

function appendGeneratedTheorems(loweredSourceText: string): string {
  const sourceFile = ts.createSourceFile("module.ts", loweredSourceText, ts.ScriptTarget.ES2022, true);
  const functionMap = buildFunctionMap(sourceFile);
  const contracts = collectContracts(sourceFile);
  const theoremNameByImplementation = new Map<string, string>();

  for (const contract of contracts.values()) {
    if (!contract.isSpec && contract.specification !== undefined) {
      theoremNameByImplementation.set(contract.name, `${contract.name}MatchesSpec`);
    }
  }

  const appendedSections: string[] = [
    "",
    "function __proofscriptEqual(left: unknown, right: unknown): boolean {",
    "  if (left === right) {",
    "    return true;",
    "  }",
    "  if (ArrayBuffer.isView(left) && ArrayBuffer.isView(right)) {",
    "    if (left.byteLength !== right.byteLength) {",
    "      return false;",
    "    }",
    "    const leftView = new Uint8Array(left.buffer, left.byteOffset, left.byteLength);",
    "    const rightView = new Uint8Array(right.buffer, right.byteOffset, right.byteLength);",
    "    for (let index = 0; index < leftView.length; index += 1) {",
    "      if (leftView[index] !== rightView[index]) {",
    "        return false;",
    "      }",
    "    }",
    "    return true;",
    "  }",
    "  if (Array.isArray(left) && Array.isArray(right)) {",
    "    if (left.length !== right.length) {",
    "      return false;",
    "    }",
    "    for (let index = 0; index < left.length; index += 1) {",
    "      if (!__proofscriptEqual(left[index], right[index])) {",
    "        return false;",
    "      }",
    "    }",
    "    return true;",
    "  }",
    "  return JSON.stringify(left) === JSON.stringify(right);",
    "}",
  ];

  for (const contract of contracts.values()) {
    if (contract.isSpec || contract.specification === undefined) {
      continue;
    }
    const implementation = contract.declaration;
    const specification = functionMap.get(contract.specification);
    if (specification === undefined) {
      throw new Error(`ProofScript could not find specification function ${contract.specification} for ${contract.name}`);
    }

    const theoremName = theoremNameByImplementation.get(contract.name);
    if (theoremName === undefined) {
      continue;
    }

    const { kind, metadata } = inferProofKind(implementation, specification);
    const dependencies = inferDependencies(implementation, specification, theoremNameByImplementation, contracts);
    appendedSections.push(
      "",
      ...theoremCommentLines(theoremName, contract.name, contract.specification, kind, dependencies, metadata),
    );
    if (kind === "exhaustive") {
      appendedSections.push(renderExhaustiveTheoremBody(implementation, contract.specification));
    } else {
      appendedSections.push(`export function ${theoremName}(): boolean {\n  return true;\n}`);
    }
  }

  return `${loweredSourceText}\n${appendedSections.join("\n")}\n`;
}

export function prepareProofScriptSource(sourceText: string): string {
  const lowered = lowerSurfaceSyntax(sourceText);
  return appendGeneratedTheorems(lowered.sourceText);
}
