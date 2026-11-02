import ts from "typescript";

export interface LoopJoinTailSchema {
  accumulator: string;
  separator: string;
  loopHelper: string;
  tailHelpers: string[];
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

function parsePushCall(statement: ts.Statement, accumulator: string): string {
  if (!ts.isExpressionStatement(statement) || !ts.isCallExpression(statement.expression)) {
    throw new Error("ProofScript loopJoinTail checker expected a push call");
  }
  const pushCall = statement.expression;
  if (
    !ts.isPropertyAccessExpression(pushCall.expression) ||
    !ts.isIdentifier(pushCall.expression.expression) ||
    pushCall.expression.expression.text !== accumulator ||
    pushCall.expression.name.text !== "push"
  ) {
    throw new Error("ProofScript loopJoinTail checker expected accumulator.push(...)");
  }
  const [argument] = pushCall.arguments;
  if (argument === undefined || !ts.isCallExpression(argument) || !ts.isIdentifier(argument.expression)) {
    throw new Error("ProofScript loopJoinTail checker expected push(helper(...))");
  }
  return argument.expression.text;
}

function parseJoinReturn(statement: ts.Statement, accumulator: string): string {
  if (!ts.isReturnStatement(statement) || statement.expression === undefined) {
    throw new Error("ProofScript loopJoinTail checker expected a return statement");
  }
  if (
    !ts.isCallExpression(statement.expression) ||
    !ts.isPropertyAccessExpression(statement.expression.expression) ||
    !ts.isIdentifier(statement.expression.expression.expression) ||
    statement.expression.expression.expression.text !== accumulator ||
    statement.expression.expression.name.text !== "join"
  ) {
    throw new Error("ProofScript loopJoinTail checker expected accumulator.join(...)");
  }
  const [separator] = statement.expression.arguments;
  if (separator === undefined || !ts.isStringLiteral(separator)) {
    throw new Error("ProofScript loopJoinTail checker expected a string join separator");
  }
  return separator.text;
}

function collectTailHelpers(statement: ts.Statement | undefined, accumulator: string, helpers: string[]): void {
  if (statement === undefined) {
    return;
  }
  if (!ts.isIfStatement(statement)) {
    throw new Error("ProofScript loopJoinTail checker expected an if/else-if tail chain");
  }
  if (!ts.isBlock(statement.thenStatement) || statement.thenStatement.statements.length === 0) {
    throw new Error("ProofScript loopJoinTail checker expected a block-bodied tail branch");
  }
  helpers.push(parsePushCall(statement.thenStatement.statements[statement.thenStatement.statements.length - 1], accumulator));
  collectTailHelpers(statement.elseStatement, accumulator, helpers);
}

export function analyzeLoopJoinTailFunction(declaration: ts.FunctionDeclaration): LoopJoinTailSchema {
  if (declaration.body === undefined) {
    throw new Error("ProofScript loopJoinTail checker requires a function body");
  }

  const statements = declaration.body.statements;
  const accumulator = statements.map(parseAccumulatorDeclaration).find((name) => name !== undefined);
  if (accumulator === undefined) {
    throw new Error("ProofScript loopJoinTail checker could not find an accumulator array");
  }

  const forStatement = statements.find((statement): statement is ts.ForStatement => ts.isForStatement(statement));
  if (forStatement === undefined || !ts.isBlock(forStatement.statement) || forStatement.statement.statements.length === 0) {
    throw new Error("ProofScript loopJoinTail checker expected a non-empty block-bodied for loop");
  }
  const loopHelper = parsePushCall(forStatement.statement.statements[forStatement.statement.statements.length - 1], accumulator);

  const topLevelIf = statements.find((statement): statement is ts.IfStatement => ts.isIfStatement(statement));
  if (topLevelIf === undefined) {
    throw new Error("ProofScript loopJoinTail checker expected a tail branch chain");
  }
  const tailHelpers: string[] = [];
  collectTailHelpers(topLevelIf, accumulator, tailHelpers);

  const separator = parseJoinReturn(statements[statements.length - 1], accumulator);

  return {
    accumulator,
    separator,
    loopHelper,
    tailHelpers,
  };
}
