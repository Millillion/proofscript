import ts from "typescript";

export interface LoopJoinSchema {
  accumulator: string;
  helper: string;
  separator: string;
}

function parseAccumulatorDeclaration(statement: ts.Statement): string | undefined {
  if (!ts.isVariableStatement(statement) || statement.declarationList.declarations.length !== 1) {
    return undefined;
  }
  const declaration = statement.declarationList.declarations[0];
  if (
    !ts.isIdentifier(declaration.name) ||
    declaration.initializer === undefined ||
    !ts.isArrayLiteralExpression(declaration.initializer) ||
    declaration.initializer.elements.length !== 0
  ) {
    return undefined;
  }
  return declaration.name.text;
}

function parseJoinReturn(statement: ts.Statement, accumulator: string): string {
  if (!ts.isReturnStatement(statement) || statement.expression === undefined) {
    throw new Error("ProofScript loopJoin checker expected a return statement");
  }
  if (
    !ts.isCallExpression(statement.expression) ||
    !ts.isPropertyAccessExpression(statement.expression.expression) ||
    !ts.isIdentifier(statement.expression.expression.expression) ||
    statement.expression.expression.expression.text !== accumulator ||
    statement.expression.expression.name.text !== "join"
  ) {
    throw new Error("ProofScript loopJoin checker expected accumulator.join(...)");
  }
  const [separator] = statement.expression.arguments;
  if (separator === undefined || !ts.isStringLiteral(separator)) {
    throw new Error("ProofScript loopJoin checker expected a string join separator");
  }
  return separator.text;
}

function parsePushCall(statement: ts.Statement, accumulator: string): string {
  if (!ts.isExpressionStatement(statement) || !ts.isCallExpression(statement.expression)) {
    throw new Error("ProofScript loopJoin checker expected a push call");
  }
  const pushCall = statement.expression;
  if (
    !ts.isPropertyAccessExpression(pushCall.expression) ||
    !ts.isIdentifier(pushCall.expression.expression) ||
    pushCall.expression.expression.text !== accumulator ||
    pushCall.expression.name.text !== "push"
  ) {
    throw new Error("ProofScript loopJoin checker expected accumulator.push(...)");
  }
  const [argument] = pushCall.arguments;
  if (argument === undefined || !ts.isCallExpression(argument) || !ts.isIdentifier(argument.expression)) {
    throw new Error("ProofScript loopJoin checker expected push(helper(...))");
  }
  return argument.expression.text;
}

export function analyzeLoopJoinFunction(declaration: ts.FunctionDeclaration): LoopJoinSchema {
  if (declaration.body === undefined) {
    throw new Error("ProofScript loopJoin checker requires a function body");
  }

  const statements = declaration.body.statements;
  const accumulator = statements.map(parseAccumulatorDeclaration).find((name) => name !== undefined);
  if (accumulator === undefined) {
    throw new Error("ProofScript loopJoin checker could not find an accumulator array");
  }

  const forStatement = statements.find((statement): statement is ts.ForStatement => ts.isForStatement(statement));
  if (forStatement === undefined || !ts.isBlock(forStatement.statement)) {
    throw new Error("ProofScript loopJoin checker expected a block-bodied for loop");
  }

  const loopStatements = forStatement.statement.statements;
  if (loopStatements.length === 0) {
    throw new Error("ProofScript loopJoin checker expected a non-empty loop body");
  }

  const helper = parsePushCall(loopStatements[loopStatements.length - 1], accumulator);
  const separator = parseJoinReturn(statements[statements.length - 1], accumulator);

  return {
    accumulator,
    helper,
    separator,
  };
}
