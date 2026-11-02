import ts from "typescript";

export type StepMode = "stringConcat" | "arraySpreadCall" | "arrayHeadAndSpread";
export type EmptyKind = "string" | "array";

export interface RecursiveChunkSchema {
  functionName: string;
  inputName: string;
  chunkSize: number;
  emptyKind: EmptyKind;
  stepMode: StepMode;
  tailHelpers: Map<number, string>;
  stepHelper: string;
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
  throw new Error("ProofScript recursive chunk checker expected a direct return");
}

function parseLengthCase(expression: ts.Expression, inputName: string): number {
  if (!ts.isBinaryExpression(expression) || expression.operatorToken.kind !== ts.SyntaxKind.EqualsEqualsEqualsToken) {
    throw new Error("ProofScript recursive chunk checker expected strict length equality");
  }
  if (
    !ts.isPropertyAccessExpression(expression.left) ||
    !ts.isIdentifier(expression.left.expression) ||
    expression.left.expression.text !== inputName ||
    expression.left.name.text !== "length"
  ) {
    throw new Error("ProofScript recursive chunk checker expected input.length");
  }
  if (!ts.isNumericLiteral(expression.right)) {
    throw new Error("ProofScript recursive chunk checker expected numeric length literal");
  }
  return Number(expression.right.text);
}

function parseCallName(expression: ts.Expression): string {
  if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
    throw new Error("ProofScript recursive chunk checker expected helper call");
  }
  return expression.expression.text;
}

function expectIndexedArguments(expression: ts.Expression, inputName: string, count: number): void {
  if (!ts.isCallExpression(expression)) {
    throw new Error("ProofScript recursive chunk checker expected a call expression");
  }
  if (expression.arguments.length !== count) {
    throw new Error("ProofScript recursive chunk checker found unexpected argument count");
  }
  expression.arguments.forEach((argument, index) => {
    if (
      !ts.isElementAccessExpression(argument) ||
      !ts.isIdentifier(argument.expression) ||
      argument.expression.text !== inputName ||
      argument.argumentExpression === undefined ||
      !ts.isNumericLiteral(argument.argumentExpression) ||
      Number(argument.argumentExpression.text) !== index
    ) {
      throw new Error("ProofScript recursive chunk checker expected prefix indexing arguments");
    }
  });
}

function isRecursiveCall(
  expression: ts.Expression,
  functionName: string,
  inputName: string,
  chunkSize: number,
): boolean {
  if (!ts.isCallExpression(expression) || !ts.isIdentifier(expression.expression)) {
    return false;
  }
  if (expression.expression.text !== functionName || expression.arguments.length !== 1) {
    return false;
  }
  const [argument] = expression.arguments;
  if (
    !ts.isCallExpression(argument) ||
    !ts.isPropertyAccessExpression(argument.expression) ||
    !ts.isIdentifier(argument.expression.expression) ||
    argument.expression.expression.text !== inputName ||
    argument.expression.name.text !== "slice" ||
    argument.arguments.length !== 1 ||
    !ts.isNumericLiteral(argument.arguments[0]) ||
    Number(argument.arguments[0].text) !== chunkSize
  ) {
    return false;
  }
  return true;
}

function parseTailExpression(expression: ts.Expression, inputName: string, caseLength: number): string | EmptyKind {
  if (caseLength === 0) {
    if (ts.isStringLiteral(expression) && expression.text === "") {
      return "string";
    }
    if (ts.isArrayLiteralExpression(expression) && expression.elements.length === 0) {
      return "array";
    }
    throw new Error("ProofScript recursive chunk checker expected empty string or empty array");
  }

  const helperName = parseCallName(expression);
  expectIndexedArguments(expression, inputName, caseLength);
  return helperName;
}

function parseStepExpression(
  expression: ts.Expression,
  functionName: string,
  inputName: string,
  chunkSize: number,
): { helperName: string; stepMode: StepMode } {
  if (ts.isBinaryExpression(expression) && expression.operatorToken.kind === ts.SyntaxKind.PlusToken) {
    const helperName = parseCallName(expression.left);
    expectIndexedArguments(expression.left, inputName, chunkSize);
    if (!isRecursiveCall(expression.right, functionName, inputName, chunkSize)) {
      throw new Error("ProofScript recursive chunk checker expected recursive suffix call");
    }
    return { helperName, stepMode: "stringConcat" };
  }

  if (ts.isArrayLiteralExpression(expression) && expression.elements.length === 2) {
    const [first, second] = expression.elements;
    if (!ts.isSpreadElement(second) || !isRecursiveCall(second.expression, functionName, inputName, chunkSize)) {
      throw new Error("ProofScript recursive chunk checker expected array recursion in final spread");
    }

    if (ts.isSpreadElement(first)) {
      const helperName = parseCallName(first.expression);
      expectIndexedArguments(first.expression, inputName, chunkSize);
      return { helperName, stepMode: "arraySpreadCall" };
    }

    const helperName = parseCallName(first);
    expectIndexedArguments(first, inputName, chunkSize);
    return { helperName, stepMode: "arrayHeadAndSpread" };
  }

  throw new Error("ProofScript recursive chunk checker found unsupported recursive step");
}

export function analyzeRecursiveChunkFunction(
  declaration: ts.FunctionDeclaration,
  inputName: string,
  chunkSize: number,
): RecursiveChunkSchema {
  if (declaration.body === undefined || declaration.name === undefined) {
    throw new Error("ProofScript recursive chunk checker requires named function bodies");
  }

  const statements = [...declaration.body.statements];
  if (statements.length === 0) {
    throw new Error("ProofScript recursive chunk checker requires a non-empty function body");
  }

  const finalStatement = statements.pop();
  if (finalStatement === undefined || !ts.isReturnStatement(finalStatement) || finalStatement.expression === undefined) {
    throw new Error("ProofScript recursive chunk checker expected a final return statement");
  }

  const tailHelpers = new Map<number, string>();
  let emptyKind: EmptyKind | undefined;

  for (const statement of statements) {
    if (!ts.isIfStatement(statement)) {
      throw new Error("ProofScript recursive chunk checker expected leading if statements");
    }
    const caseLength = parseLengthCase(statement.expression, inputName);
    const parsed = parseTailExpression(unwrapReturn(statement.thenStatement), inputName, caseLength);
    if (caseLength === 0) {
      emptyKind = parsed as EmptyKind;
      continue;
    }
    if (typeof parsed !== "string") {
      throw new Error("ProofScript recursive chunk checker encountered invalid tail helper");
    }
    tailHelpers.set(caseLength, parsed);
  }

  if (emptyKind === undefined) {
    throw new Error("ProofScript recursive chunk checker requires an explicit empty case");
  }

  const { helperName: stepHelper, stepMode } = parseStepExpression(
    finalStatement.expression,
    declaration.name.text,
    inputName,
    chunkSize,
  );

  return {
    functionName: declaration.name.text,
    inputName,
    chunkSize,
    emptyKind,
    stepMode,
    tailHelpers,
    stepHelper,
  };
}
