import ts from "typescript";

export interface LoopWriteSchema {
  accumulator: string;
  indexer: string;
  writesPerIteration: number;
  tailWrites: number[];
}

function parseAccumulatorDeclaration(statement: ts.Statement): string | undefined {
  if (!ts.isVariableStatement(statement) || statement.declarationList.declarations.length !== 1) {
    return undefined;
  }
  const declaration = statement.declarationList.declarations[0];
  if (
    !ts.isIdentifier(declaration.name) ||
    declaration.initializer === undefined ||
    !ts.isNewExpression(declaration.initializer)
  ) {
    return undefined;
  }
  return declaration.name.text;
}

function readAccumulatorWriteIndexer(statement: ts.Statement, accumulator: string): string | undefined {
  if (!ts.isExpressionStatement(statement) || !ts.isBinaryExpression(statement.expression)) {
    return undefined;
  }
  const assignment = statement.expression;
  if (assignment.operatorToken.kind !== ts.SyntaxKind.EqualsToken) {
    return undefined;
  }
  if (!ts.isElementAccessExpression(assignment.left) || assignment.left.argumentExpression === undefined) {
    return undefined;
  }
  if (!ts.isIdentifier(assignment.left.expression) || assignment.left.expression.text !== accumulator) {
    return undefined;
  }
  const indexExpression = assignment.left.argumentExpression;
  if (
    ts.isPostfixUnaryExpression(indexExpression) &&
    indexExpression.operator === ts.SyntaxKind.PlusPlusToken &&
    ts.isIdentifier(indexExpression.operand) &&
    indexExpression.operand.text.length > 0
  ) {
    return indexExpression.operand.text;
  }
  return undefined;
}

function isAccumulatorWrite(statement: ts.Statement, accumulator: string, indexer: string): boolean {
  return readAccumulatorWriteIndexer(statement, accumulator) === indexer;
}

function inferIndexer(statements: readonly ts.Statement[], accumulator: string): string | undefined {
  for (const statement of statements) {
    const indexer = readAccumulatorWriteIndexer(statement, accumulator);
    if (indexer !== undefined) {
      return indexer;
    }
  }
  return undefined;
}

function countWrites(statements: readonly ts.Statement[], accumulator: string, indexer: string): number {
  return statements.filter((statement) => isAccumulatorWrite(statement, accumulator, indexer)).length;
}

function parseReturn(statement: ts.Statement, accumulator: string): void {
  if (
    !ts.isReturnStatement(statement) ||
    statement.expression === undefined ||
    !ts.isIdentifier(statement.expression) ||
    statement.expression.text !== accumulator
  ) {
    throw new Error("ProofScript loopWrite checker expected a final return of the accumulator");
  }
}

export function analyzeLoopWriteFunction(declaration: ts.FunctionDeclaration): LoopWriteSchema {
  if (declaration.body === undefined) {
    throw new Error("ProofScript loopWrite checker requires a function body");
  }

  const statements = declaration.body.statements;
  const accumulator = statements.map(parseAccumulatorDeclaration).find((name) => name !== undefined);
  if (accumulator === undefined) {
    throw new Error("ProofScript loopWrite checker could not find the accumulator array");
  }

  const forStatement = statements.find((statement): statement is ts.ForStatement => ts.isForStatement(statement));
  if (forStatement === undefined || !ts.isBlock(forStatement.statement)) {
    throw new Error("ProofScript loopWrite checker expected a block-bodied for loop");
  }

  const indexer = inferIndexer(forStatement.statement.statements, accumulator);
  if (indexer === undefined) {
    throw new Error("ProofScript loopWrite checker could not find the cursor variable");
  }

  const writesPerIteration = countWrites(forStatement.statement.statements, accumulator, indexer);
  if (writesPerIteration === 0) {
    throw new Error("ProofScript loopWrite checker expected loop writes to the accumulator");
  }

  const tailWrites = statements
    .filter((statement): statement is ts.IfStatement => ts.isIfStatement(statement))
    .map((statement) => {
      if (!ts.isBlock(statement.thenStatement)) {
        throw new Error("ProofScript loopWrite checker expected block-bodied tail cases");
      }
      const writes = countWrites(statement.thenStatement.statements, accumulator, indexer);
      if (writes === 0) {
        throw new Error("ProofScript loopWrite checker expected accumulator writes in each tail case");
      }
      return writes;
    });

  parseReturn(statements[statements.length - 1], accumulator);

  return {
    accumulator,
    indexer,
    writesPerIteration,
    tailWrites,
  };
}
