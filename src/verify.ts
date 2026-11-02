import { mkdir, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { pathToFileURL } from "node:url";

import ts from "typescript";

import { collectTheorems, type TheoremAnnotation } from "./annotations.js";
import { prepareProofScriptSource } from "./frontend.js";
import { getFiniteDomain } from "./domains.js";
import { assertEquivalentFunctions } from "./equivalence.js";
import { analyzeLoopJoinFunction } from "./loop-join.js";
import { analyzeLoopJoinTailFunction } from "./loop-join-tail.js";
import { analyzeLoopWriteFunction } from "./loop-write.js";
import { analyzeRecursiveAdvanceFunction } from "./recursive-advance.js";
import type {
  CompositionProofArtifact,
  ExhaustiveProofArtifact,
  LoopJoinProofArtifact,
  LoopJoinTailProofArtifact,
  LoopWriteProofArtifact,
  ProofArtifact,
  RecursiveAdvanceProofArtifact,
  TheoremArtifact,
} from "./proof-artifacts.js";
import { analyzeRecursiveChunkFunction } from "./schema.js";

export interface VerificationResult {
  emittedJavaScriptPath: string;
  proofArtifactPath: string;
  proofArtifact: ProofArtifact;
}

interface PreparedSource {
  absoluteSourcePath: string;
  loweredSourceText: string;
  sourceFile: ts.SourceFile;
}

function formatDiagnostics(diagnostics: readonly ts.Diagnostic[]): string {
  return ts.formatDiagnosticsWithColorAndContext(diagnostics, {
    getCanonicalFileName: (fileName) => fileName,
    getCurrentDirectory: () => process.cwd(),
    getNewLine: () => "\n",
  });
}

function expectIdentifierName(parameter: ts.ParameterDeclaration): string {
  if (!ts.isIdentifier(parameter.name)) {
    throw new Error("ProofScript only supports identifier theorem parameters");
  }
  return parameter.name.text;
}

async function prepareSource(sourcePath: string): Promise<PreparedSource> {
  const absoluteSourcePath = path.resolve(sourcePath);
  const rawSourceText = await ts.sys.readFile(absoluteSourcePath);
  if (rawSourceText === undefined) {
    throw new Error(`ProofScript could not read ${absoluteSourcePath}`);
  }
  const loweredSourceText = prepareProofScriptSource(rawSourceText);
  const sourceFile = ts.createSourceFile(absoluteSourcePath, loweredSourceText, ts.ScriptTarget.ES2022, true);
  return {
    absoluteSourcePath,
    loweredSourceText,
    sourceFile,
  };
}

export async function compileProofScriptModule(sourcePath: string): Promise<string> {
  const preparedSource = await prepareSource(sourcePath);
  const absoluteSourcePath = preparedSource.absoluteSourcePath;
  const buildRoot = path.resolve(".proofscript-build");
  const sourceRoot = path.dirname(absoluteSourcePath);

  await rm(buildRoot, { recursive: true, force: true });
  await mkdir(buildRoot, { recursive: true });

  const compilerOptions: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    outDir: buildRoot,
    rootDir: sourceRoot,
    strict: true,
    esModuleInterop: true,
    noEmitOnError: true,
    skipLibCheck: true,
  };

  const host = ts.createCompilerHost(compilerOptions);
  const originalGetSourceFile = host.getSourceFile.bind(host);
  const originalReadFile = host.readFile.bind(host);

  host.readFile = (fileName) => {
    if (path.resolve(fileName) === absoluteSourcePath) {
      return preparedSource.loweredSourceText;
    }
    return originalReadFile(fileName);
  };

  host.getSourceFile = (fileName, languageVersion, onError, shouldCreateNewSourceFile) => {
    if (path.resolve(fileName) === absoluteSourcePath) {
      return ts.createSourceFile(fileName, preparedSource.loweredSourceText, languageVersion, true);
    }
    return originalGetSourceFile(fileName, languageVersion, onError, shouldCreateNewSourceFile);
  };

  const program = ts.createProgram([absoluteSourcePath], compilerOptions, host);
  const diagnostics = ts.getPreEmitDiagnostics(program);
  if (diagnostics.length > 0) {
    throw new Error(formatDiagnostics(diagnostics));
  }

  const emitResult = program.emit();
  if (emitResult.emitSkipped) {
    throw new Error("ProofScript failed to emit JavaScript");
  }

  const outputFileName = path.basename(absoluteSourcePath).replace(/\.tsx?$/u, ".js");
  return path.join(buildRoot, outputFileName);
}

async function importModule(emittedJavaScriptPath: string): Promise<Record<string, unknown>> {
  const url = pathToFileURL(emittedJavaScriptPath);
  url.searchParams.set("t", `${Date.now()}`);
  return (await import(url.href)) as Record<string, unknown>;
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

function verifyExhaustiveTheorem(
  annotation: TheoremAnnotation,
  exportedModule: Record<string, unknown>,
): ExhaustiveProofArtifact {
  const theorem = exportedModule[annotation.name];
  if (typeof theorem !== "function") {
    throw new Error(`ProofScript theorem ${annotation.name} is not an exported function`);
  }

  const bindings = annotation.declaration.parameters.map((parameter) => {
    const name = expectIdentifierName(parameter);
    const binding = annotation.domains.find((entry) => entry.name === name);
    if (binding === undefined) {
      throw new Error(`ProofScript theorem ${annotation.name} is missing a domain for ${name}`);
    }
    return binding;
  });

  if (bindings.length === 0) {
    throw new Error(`ProofScript exhaustive theorem ${annotation.name} requires finite domains`);
  }

  const domainValues = bindings.map((binding) => getFiniteDomain(binding.domain).values);
  const indices = Array.from({ length: bindings.length }, () => 0);
  let checkedCases = 0;

  while (true) {
    const args = domainValues.map((values, index) => values[indices[index]]);
    const passed = theorem(...args);
    checkedCases += 1;
    if (passed !== true) {
      throw new Error(
        `ProofScript theorem ${annotation.name} failed for ${JSON.stringify(
          Object.fromEntries(bindings.map((binding, index) => [binding.name, args[index]])),
        )}`,
      );
    }

    let cursor = indices.length - 1;
    while (cursor >= 0) {
      indices[cursor] += 1;
      if (indices[cursor] < domainValues[cursor].length) {
        break;
      }
      indices[cursor] = 0;
      cursor -= 1;
    }
    if (cursor < 0) {
      break;
    }
  }

  return {
    name: annotation.name,
    kind: "exhaustive",
    implementation: annotation.implementation,
    specification: annotation.specification,
    checkedCases,
    bindings,
  };
}

function resolveFunction(
  name: string | undefined,
  functionMap: Map<string, ts.FunctionDeclaration>,
  theoremName: string,
): ts.FunctionDeclaration {
  if (name === undefined) {
    throw new Error(`ProofScript theorem ${theoremName} is missing a function reference`);
  }
  const declaration = functionMap.get(name);
  if (declaration === undefined) {
    throw new Error(`ProofScript could not find function ${name} referenced by ${theoremName}`);
  }
  return declaration;
}

function dependencyPairs(
  annotation: TheoremAnnotation,
  verifiedTheorems: Map<string, TheoremArtifact>,
): Map<string, string> {
  const pairs = new Map<string, string>();
  for (const dependencyName of annotation.dependencies) {
    const dependency = verifiedTheorems.get(dependencyName);
    if (dependency === undefined) {
      throw new Error(`ProofScript theorem ${annotation.name} is waiting on ${dependencyName}`);
    }
    if (dependency.implementation === undefined || dependency.specification === undefined) {
      throw new Error(`ProofScript dependency ${dependency.name} does not expose function equivalence metadata`);
    }
    pairs.set(dependency.implementation, dependency.specification);
  }
  return pairs;
}

function verifyRecursiveChunkTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): TheoremArtifact {
  if (annotation.input === undefined || annotation.chunkSize === undefined) {
    throw new Error(`ProofScript recursive theorem ${annotation.name} is missing @proofInput or @proofChunkSize`);
  }

  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);

  const implementationSchema = analyzeRecursiveChunkFunction(
    implementation,
    annotation.input,
    annotation.chunkSize,
  );
  const specificationSchema = analyzeRecursiveChunkFunction(
    specification,
    annotation.input,
    annotation.chunkSize,
  );

  if (implementationSchema.emptyKind !== specificationSchema.emptyKind) {
    throw new Error(`ProofScript recursive theorem ${annotation.name} has mismatched empty cases`);
  }
  if (implementationSchema.stepMode !== specificationSchema.stepMode) {
    throw new Error(`ProofScript recursive theorem ${annotation.name} has mismatched recursive step modes`);
  }

  const implementationTailLengths = [...implementationSchema.tailHelpers.keys()].sort((left, right) => left - right);
  const specificationTailLengths = [...specificationSchema.tailHelpers.keys()].sort((left, right) => left - right);
  const annotatedTailLengths = [...annotation.tailLengths].sort((left, right) => left - right);

  if (JSON.stringify(implementationTailLengths) !== JSON.stringify(specificationTailLengths)) {
    throw new Error(`ProofScript recursive theorem ${annotation.name} has mismatched tail cases`);
  }
  if (JSON.stringify(implementationTailLengths) !== JSON.stringify(annotatedTailLengths)) {
    throw new Error(`ProofScript recursive theorem ${annotation.name} does not match its annotated tail lengths`);
  }

  const pairs = dependencyPairs(annotation, verifiedTheorems);
  for (const tailLength of implementationTailLengths) {
    const implementationHelper = implementationSchema.tailHelpers.get(tailLength);
    const specificationHelper = specificationSchema.tailHelpers.get(tailLength);
    if (implementationHelper === undefined || specificationHelper === undefined) {
      throw new Error(`ProofScript recursive theorem ${annotation.name} is missing tail helpers`);
    }
    if (implementationHelper === specificationHelper) {
      continue;
    }
    const mappedHelper = pairs.get(implementationHelper);
    if (mappedHelper !== specificationHelper) {
      throw new Error(
        `ProofScript recursive theorem ${annotation.name} is missing proof support for ${implementationHelper} ~ ${specificationHelper}`,
      );
    }
  }

  if (implementationSchema.stepHelper !== specificationSchema.stepHelper) {
    const mappedStepHelper = pairs.get(implementationSchema.stepHelper);
    if (mappedStepHelper !== specificationSchema.stepHelper) {
      throw new Error(
        `ProofScript recursive theorem ${annotation.name} is missing proof support for ${implementationSchema.stepHelper} ~ ${specificationSchema.stepHelper}`,
      );
    }
  }

  return {
    name: annotation.name,
    kind: "recursiveChunk",
    implementation: annotation.implementation,
    specification: annotation.specification,
    input: annotation.input,
    chunkSize: annotation.chunkSize,
    tailLengths: annotatedTailLengths,
    dependencies: [...annotation.dependencies],
  };
}

function verifyRecursiveAdvanceTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): RecursiveAdvanceProofArtifact {
  if (annotation.input === undefined || annotation.index === undefined) {
    throw new Error(`ProofScript recursiveAdvance theorem ${annotation.name} is missing @proofInput or @proofIndex`);
  }

  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);
  const implementationSchema = analyzeRecursiveAdvanceFunction(implementation, annotation.input, annotation.index);
  const specificationSchema = analyzeRecursiveAdvanceFunction(specification, annotation.input, annotation.index);

  if (implementationSchema.baseReturn !== specificationSchema.baseReturn) {
    throw new Error(`ProofScript recursiveAdvance theorem ${annotation.name} has mismatched base returns`);
  }
  if (implementationSchema.matchLiteral !== specificationSchema.matchLiteral) {
    throw new Error(`ProofScript recursiveAdvance theorem ${annotation.name} has mismatched match literals`);
  }
  if (implementationSchema.matchReturn !== specificationSchema.matchReturn) {
    throw new Error(`ProofScript recursiveAdvance theorem ${annotation.name} has mismatched match returns`);
  }

  const pairs = dependencyPairs(annotation, verifiedTheorems);
  if (implementationSchema.helper !== specificationSchema.helper) {
    const mappedHelper = pairs.get(implementationSchema.helper);
    if (mappedHelper !== specificationSchema.helper) {
      throw new Error(
        `ProofScript recursiveAdvance theorem ${annotation.name} is missing proof support for ${implementationSchema.helper} ~ ${specificationSchema.helper}`,
      );
    }
  }

  return {
    name: annotation.name,
    kind: "recursiveAdvance",
    implementation: annotation.implementation,
    specification: annotation.specification,
    input: annotation.input,
    index: annotation.index,
    dependencies: [...annotation.dependencies],
  };
}

function verifyCompositionTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): CompositionProofArtifact {
  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);
  const pairs = dependencyPairs(annotation, verifiedTheorems);
  assertEquivalentFunctions(implementation, specification, pairs);

  return {
    name: annotation.name,
    kind: "composition",
    implementation: annotation.implementation,
    specification: annotation.specification,
    dependencies: [...annotation.dependencies],
  };
}

function verifyLoopJoinTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): LoopJoinProofArtifact {
  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);
  const implementationSchema = analyzeLoopJoinFunction(implementation);
  const specificationSchema = analyzeLoopJoinFunction(specification);

  if (implementationSchema.accumulator !== specificationSchema.accumulator) {
    throw new Error(`ProofScript loopJoin theorem ${annotation.name} has mismatched accumulators`);
  }
  if (implementationSchema.separator !== specificationSchema.separator) {
    throw new Error(`ProofScript loopJoin theorem ${annotation.name} has mismatched join separators`);
  }

  const pairs = dependencyPairs(annotation, verifiedTheorems);
  if (implementationSchema.helper !== specificationSchema.helper) {
    const mappedHelper = pairs.get(implementationSchema.helper);
    if (mappedHelper !== specificationSchema.helper) {
      throw new Error(
        `ProofScript loopJoin theorem ${annotation.name} is missing proof support for ${implementationSchema.helper} ~ ${specificationSchema.helper}`,
      );
    }
  }

  assertEquivalentFunctions(implementation, specification, pairs);

  return {
    name: annotation.name,
    kind: "loopJoin",
    implementation: annotation.implementation,
    specification: annotation.specification,
    accumulator: implementationSchema.accumulator,
    separator: implementationSchema.separator,
    dependencies: [...annotation.dependencies],
  };
}

function verifyLoopWriteTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): LoopWriteProofArtifact {
  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);
  const implementationSchema = analyzeLoopWriteFunction(implementation);
  const specificationSchema = analyzeLoopWriteFunction(specification);

  if (implementationSchema.accumulator !== specificationSchema.accumulator) {
    throw new Error(`ProofScript loopWrite theorem ${annotation.name} has mismatched accumulators`);
  }
  if (implementationSchema.indexer !== specificationSchema.indexer) {
    throw new Error(`ProofScript loopWrite theorem ${annotation.name} has mismatched cursor variables`);
  }
  if (implementationSchema.writesPerIteration !== specificationSchema.writesPerIteration) {
    throw new Error(`ProofScript loopWrite theorem ${annotation.name} has mismatched loop write counts`);
  }
  if (JSON.stringify(implementationSchema.tailWrites) !== JSON.stringify(specificationSchema.tailWrites)) {
    throw new Error(`ProofScript loopWrite theorem ${annotation.name} has mismatched tail write counts`);
  }

  const pairs = dependencyPairs(annotation, verifiedTheorems);
  assertEquivalentFunctions(implementation, specification, pairs);

  return {
    name: annotation.name,
    kind: "loopWrite",
    implementation: annotation.implementation,
    specification: annotation.specification,
    accumulator: implementationSchema.accumulator,
    indexer: implementationSchema.indexer,
    writesPerIteration: implementationSchema.writesPerIteration,
    tailWrites: implementationSchema.tailWrites,
    dependencies: [...annotation.dependencies],
  };
}

function verifyLoopJoinTailTheorem(
  annotation: TheoremAnnotation,
  functionMap: Map<string, ts.FunctionDeclaration>,
  verifiedTheorems: Map<string, TheoremArtifact>,
): LoopJoinTailProofArtifact {
  const implementation = resolveFunction(annotation.implementation, functionMap, annotation.name);
  const specification = resolveFunction(annotation.specification, functionMap, annotation.name);
  const implementationSchema = analyzeLoopJoinTailFunction(implementation);
  const specificationSchema = analyzeLoopJoinTailFunction(specification);

  if (implementationSchema.accumulator !== specificationSchema.accumulator) {
    throw new Error(`ProofScript loopJoinTail theorem ${annotation.name} has mismatched accumulators`);
  }
  if (implementationSchema.separator !== specificationSchema.separator) {
    throw new Error(`ProofScript loopJoinTail theorem ${annotation.name} has mismatched separators`);
  }
  if (implementationSchema.tailHelpers.length !== specificationSchema.tailHelpers.length) {
    throw new Error(`ProofScript loopJoinTail theorem ${annotation.name} has mismatched tail branch counts`);
  }

  const pairs = dependencyPairs(annotation, verifiedTheorems);
  const mappedLoopHelper = pairs.get(implementationSchema.loopHelper);
  if (
    implementationSchema.loopHelper !== specificationSchema.loopHelper &&
    mappedLoopHelper !== specificationSchema.loopHelper
  ) {
    throw new Error(
      `ProofScript loopJoinTail theorem ${annotation.name} is missing proof support for ${implementationSchema.loopHelper} ~ ${specificationSchema.loopHelper}`,
    );
  }

  for (let index = 0; index < implementationSchema.tailHelpers.length; index += 1) {
    const implementationHelper = implementationSchema.tailHelpers[index];
    const specificationHelper = specificationSchema.tailHelpers[index];
    const mappedHelper = pairs.get(implementationHelper);
    if (implementationHelper !== specificationHelper && mappedHelper !== specificationHelper) {
      throw new Error(
        `ProofScript loopJoinTail theorem ${annotation.name} is missing proof support for ${implementationHelper} ~ ${specificationHelper}`,
      );
    }
  }

  assertEquivalentFunctions(implementation, specification, pairs);

  return {
    name: annotation.name,
    kind: "loopJoinTail",
    implementation: annotation.implementation,
    specification: annotation.specification,
    accumulator: implementationSchema.accumulator,
    separator: implementationSchema.separator,
    loopHelper: implementationSchema.loopHelper,
    tailHelpers: implementationSchema.tailHelpers,
    dependencies: [...annotation.dependencies],
  };
}

export async function verifyProofScriptModule(sourcePath: string): Promise<VerificationResult> {
  const preparedSource = await prepareSource(sourcePath);
  const absoluteSourcePath = preparedSource.absoluteSourcePath;
  const theoremAnnotations = collectTheorems(preparedSource.sourceFile);
  const functionMap = buildFunctionMap(preparedSource.sourceFile);
  const emittedJavaScriptPath = await compileProofScriptModule(absoluteSourcePath);
  const exportedModule = await importModule(emittedJavaScriptPath);

  const verifiedTheorems = new Map<string, TheoremArtifact>();
  const pending = new Map(theoremAnnotations.map((annotation) => [annotation.name, annotation]));

  while (pending.size > 0) {
    let progressed = false;

    for (const [name, annotation] of [...pending.entries()]) {
      const dependenciesReady = annotation.dependencies.every((dependency) => verifiedTheorems.has(dependency));
      if (!dependenciesReady) {
        continue;
      }

      const artifact =
        annotation.kind === "exhaustive"
          ? verifyExhaustiveTheorem(annotation, exportedModule)
          : annotation.kind === "recursiveChunk"
            ? verifyRecursiveChunkTheorem(annotation, functionMap, verifiedTheorems)
            : annotation.kind === "recursiveAdvance"
              ? verifyRecursiveAdvanceTheorem(annotation, functionMap, verifiedTheorems)
            : annotation.kind === "composition"
              ? verifyCompositionTheorem(annotation, functionMap, verifiedTheorems)
              : annotation.kind === "loopJoin"
                ? verifyLoopJoinTheorem(annotation, functionMap, verifiedTheorems)
                : annotation.kind === "loopJoinTail"
                  ? verifyLoopJoinTailTheorem(annotation, functionMap, verifiedTheorems)
                  : verifyLoopWriteTheorem(annotation, functionMap, verifiedTheorems);

      verifiedTheorems.set(name, artifact);
      pending.delete(name);
      progressed = true;
    }

    if (!progressed) {
      throw new Error(
        `ProofScript could not resolve theorem dependencies: ${[...pending.keys()].join(", ")}`,
      );
    }
  }

  const proofArtifact: ProofArtifact = {
    modulePath: absoluteSourcePath,
    verifiedAt: new Date().toISOString(),
    theorems: theoremAnnotations.map((annotation) => {
      const artifact = verifiedTheorems.get(annotation.name);
      if (artifact === undefined) {
        throw new Error(`Missing theorem artifact for ${annotation.name}`);
      }
      return artifact;
    }),
  };

  const proofArtifactPath = path.resolve(
    "proof-artifacts",
    `${path.basename(absoluteSourcePath).replace(/\.(proof\.)?tsx?$/u, "")}.proof.json`,
  );
  await mkdir(path.dirname(proofArtifactPath), { recursive: true });
  await writeFile(proofArtifactPath, JSON.stringify(proofArtifact, null, 2));

  return {
    emittedJavaScriptPath,
    proofArtifactPath,
    proofArtifact,
  };
}
