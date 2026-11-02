import ts from "typescript";

import type { ProofKind } from "./proof-artifacts.js";

export interface DomainBinding {
  name: string;
  domain: string;
}

export interface TheoremAnnotation {
  name: string;
  kind: ProofKind;
  implementation?: string;
  specification?: string;
  domains: DomainBinding[];
  dependencies: string[];
  input?: string;
  index?: string;
  chunkSize?: number;
  tailLengths: number[];
  declaration: ts.FunctionDeclaration;
}

function readTagMap(node: ts.Node): Map<string, string> {
  const tagMap = new Map<string, string>();
  for (const tag of ts.getJSDocTags(node)) {
    const commentText =
      typeof tag.comment === "string"
        ? tag.comment
        : (tag.comment ?? [])
            .map((part) => ("text" in part ? part.text : ""))
            .join("")
            .trim();
    tagMap.set(tag.tagName.getText(), commentText);
  }
  return tagMap;
}

function parseProofKind(raw: string | undefined, name: string): ProofKind {
  if (
    raw === "exhaustive" ||
    raw === "recursiveChunk" ||
    raw === "recursiveAdvance" ||
    raw === "composition" ||
    raw === "loopJoin" ||
    raw === "loopJoinTail" ||
    raw === "loopWrite"
  ) {
    return raw;
  }
  throw new Error(`Function ${name} has invalid or missing @proofKind annotation`);
}

function parseDomains(raw: string | undefined): DomainBinding[] {
  if (raw === undefined || raw.trim() === "") {
    return [];
  }

  return raw
    .split(",")
    .map((entry) => entry.trim())
    .filter((entry) => entry.length > 0)
    .map((entry) => {
      const [name, domain] = entry.split(":").map((part) => part.trim());
      if (name === undefined || domain === undefined || name === "" || domain === "") {
        throw new Error(`Invalid @proofDomains entry: ${entry}`);
      }
      return { name, domain };
    });
}

function parseList(raw: string | undefined): string[] {
  if (raw === undefined || raw.trim() === "") {
    return [];
  }
  return raw
    .split(",")
    .map((entry) => entry.trim())
    .filter((entry) => entry.length > 0);
}

function parseNumberList(raw: string | undefined): number[] {
  return parseList(raw).map((entry) => {
    const parsed = Number(entry);
    if (!Number.isInteger(parsed)) {
      throw new Error(`Invalid integer in ProofScript annotation: ${entry}`);
    }
    return parsed;
  });
}

export function collectTheorems(sourceFile: ts.SourceFile): TheoremAnnotation[] {
  const theorems: TheoremAnnotation[] = [];

  const visit = (node: ts.Node): void => {
    if (ts.isFunctionDeclaration(node) && node.name !== undefined) {
      const tags = readTagMap(node);
      if (tags.has("proofKind")) {
        theorems.push({
          name: node.name.text,
          kind: parseProofKind(tags.get("proofKind"), node.name.text),
          implementation: tags.get("proofImplementation"),
          specification: tags.get("proofSpecification"),
          domains: parseDomains(tags.get("proofDomains")),
          dependencies: parseList(tags.get("proofDependencies")),
          input: tags.get("proofInput"),
          index: tags.get("proofIndex"),
          chunkSize:
            tags.get("proofChunkSize") === undefined
              ? undefined
              : Number(tags.get("proofChunkSize")),
          tailLengths: parseNumberList(tags.get("proofTailLengths")),
          declaration: node,
        });
      }
    }
    ts.forEachChild(node, visit);
  };

  visit(sourceFile);
  return theorems;
}
