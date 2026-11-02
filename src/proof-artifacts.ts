export type ProofKind =
  | "exhaustive"
  | "recursiveChunk"
  | "recursiveAdvance"
  | "composition"
  | "loopJoin"
  | "loopJoinTail"
  | "loopWrite";

export interface FiniteDomainBinding {
  name: string;
  domain: string;
}

export interface TheoremMetadata {
  name: string;
  kind: ProofKind;
  implementation?: string;
  specification?: string;
}

export interface ExhaustiveProofArtifact extends TheoremMetadata {
  kind: "exhaustive";
  checkedCases: number;
  bindings: FiniteDomainBinding[];
}

export interface RecursiveChunkProofArtifact extends TheoremMetadata {
  kind: "recursiveChunk";
  input: string;
  chunkSize: number;
  tailLengths: number[];
  dependencies: string[];
}

export interface RecursiveAdvanceProofArtifact extends TheoremMetadata {
  kind: "recursiveAdvance";
  input: string;
  index: string;
  dependencies: string[];
}

export interface CompositionProofArtifact extends TheoremMetadata {
  kind: "composition";
  dependencies: string[];
}

export interface LoopJoinProofArtifact extends TheoremMetadata {
  kind: "loopJoin";
  accumulator: string;
  separator: string;
  dependencies: string[];
}

export interface LoopJoinTailProofArtifact extends TheoremMetadata {
  kind: "loopJoinTail";
  accumulator: string;
  separator: string;
  loopHelper: string;
  tailHelpers: string[];
  dependencies: string[];
}

export interface LoopWriteProofArtifact extends TheoremMetadata {
  kind: "loopWrite";
  accumulator: string;
  indexer: string;
  writesPerIteration: number;
  tailWrites: number[];
  dependencies: string[];
}

export type TheoremArtifact =
  | ExhaustiveProofArtifact
  | RecursiveChunkProofArtifact
  | RecursiveAdvanceProofArtifact
  | CompositionProofArtifact
  | LoopJoinProofArtifact
  | LoopJoinTailProofArtifact
  | LoopWriteProofArtifact;

export interface ProofArtifact {
  modulePath: string;
  verifiedAt: string;
  theorems: TheoremArtifact[];
}
