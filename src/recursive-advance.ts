import ts from "typescript";

function literalKey(expression: ts.Expression): string {
  if (ts.isNumericLiteral(expression) || ts.isStringLiteral(expression)) {
    return `${expression.kind}:${expression.text}`;
  }
  if (
    ts.isPrefixUnaryExpression(expression) &&
    expression.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(expression.operand)
  ) {
    return `minus:${expression.operand.text}`;
  }
  throw new Error("ProofScript recursiveAdvance checker expected a literal return");
}

function unwrapReturn(statement: ts.Statement): ts.Expression {
  if (ts.isReturnStatement(statement) && statement.expression !== undefined) {
    return statement.expression;
  }
  if (
    ts.isBlock(statement) &&
    statement.statements.length === 1 &&
    ts.isReturnStatement(statement.statements[0]) &&
    statement.statements[0].expression !== undefined
  ) {
    return statement.statements[0].expression;
  }
  throw new Error("ProofScript recursiveAdvance checker expected a direct return");
}

export interface RecursiveAdvanceSchema {
  helper: string;
  baseReturn: string;
  matchLiteral: string;
  matchReturn: string;
}

function expectEndCondition(expression: ts.Expression, inputName: string, indexName: string): void {
  if (!ts.isBinaryExpression(expression) || expression.operatorToken.kind !== ts.SyntaxKind.EqualsEqualsEqualsToken) {
    throw new Error("ProofScript recursiveAdvance checker expected strict equality");
  }
  if (!ts.isIdentifier(expression.left) || expression.left.text !== indexName) {
    throw new Error("ProofScript recursiveAdvance checker expected cursor on the left side");
  }
  if (
    !ts.isPropertyAccessExpression(expression.right) ||
    !ts.isIdentifier(expression.right.expression) ||
    expression.right.expression.text !== inputName ||
    expression.right.name.text !== "length"
  ) {
    throw new Error("ProofScript recursiveAdvance checker expected input.length");
  }
}

function parseMatchCondition(expression: ts.Expression, inputName: string, indexName: string): string {
  if (!ts.isBinaryExpression(expression) || expression.operatorToken.kind !== ts.SyntaxKind.EqualsEqualsEqualsToken) {
    throw new Error("ProofScript recursiveAdvance checker expected strict equality");
  }
  if (
    !ts.isElementAccessExpression(expression.left) ||
    !ts.isIdentifier(expression.left.expression) ||
    expression.left.expression.text !== inputName ||
    expression.left.argumentExpression === undefined ||
    !ts.isIdentifier(expression.left.argumentExpression) ||
    expression.left.argumentExpression.text !== indexName
  ) {
    throw new Error("ProofScript recursiveAdvance checker expected input[index]");
  }
  if (!ts.isStringLiteral(expression.right)) {
    throw new Error("ProofScript recursiveAdvance checker expected a string match literal");
  }
  return expression.right.text;
}

function parseRecursiveHelper(
  expression: ts.Expression,
  functionName: string,
  inputName: string,
  indexName: string,
): string {
  if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
    throw new Error("ProofScript recursiveAdvance checker expected helper(recursiveCall(...))");
  }
  const helperName = expression.expression.text;
  if (expression.arguments.length !== 1) {
    throw new Error("ProofScript recursiveAdvance checker expected unary helper application");
  }
  const [argument] = expression.arguments;
  if (!ts.isCallExpression(argument) || !ts.isIdentifier(argument.expression) || argument.expression.text !== functionName) {
    throw new Error("ProofScript recursiveAdvance checker expected a recursive call");
  }
  if (argument.arguments.length !== 2) {
    throw new Error("ProofScript recursiveAdvance checker expected recursive call arity 2");
  }
  if (!ts.isIdentifier(argument.arguments[0]) || argument.arguments[0].text !== inputName) {
    throw new Error("ProofScript recursiveAdvance checker expected the original input to be threaded through");
  }
  const cursorArgument = argument.arguments[1];
  if (
    !ts.isBinaryExpression(cursorArgument) ||
    cursorArgument.operatorToken.kind !== ts.SyntaxKind.PlusToken ||
    !ts.isIdentifier(cursorArgument.left) ||
    cursorArgument.left.text !== indexName ||
    !ts.isNumericLiteral(cursorArgument.right) ||
    cursorArgument.right.text !== "1"
  ) {
    throw new Error("ProofScript recursiveAdvance checker expected index + 1 recursion");
  }
  return helperName;
}

export function analyzeRecursiveAdvanceFunction(
  declaration: ts.FunctionDeclaration,
  inputName: string,
  indexName: string,
): RecursiveAdvanceSchema {
  if (declaration.body === undefined || declaration.name === undefined) {
    throw new Error("ProofScript recursiveAdvance checker requires a named function body");
  }

  const statements = declaration.body.statements;
  if (statements.length !== 3) {
    throw new Error("ProofScript recursiveAdvance checker expected exactly two if statements and a return");
  }

  const [endCase, matchCase, recursiveReturn] = statements;
  if (!ts.isIfStatement(endCase) || !ts.isIfStatement(matchCase) || !ts.isReturnStatement(recursiveReturn)) {
    throw new Error("ProofScript recursiveAdvance checker expected if/if/return structure");
  }

  expectEndCondition(endCase.expression, inputName, indexName);
  const baseReturn = literalKey(unwrapReturn(endCase.thenStatement));

  const matchLiteral = parseMatchCondition(matchCase.expression, inputName, indexName);
  const matchReturn = literalKey(unwrapReturn(matchCase.thenStatement));

  if (recursiveReturn.expression === undefined) {
    throw new Error("ProofScript recursiveAdvance checker expected a recursive return expression");
  }
  const helper = parseRecursiveHelper(recursiveReturn.expression, declaration.name.text, inputName, indexName);

  return {
    helper,
    baseReturn,
    matchLiteral,
    matchReturn,
  };
}
