import ts from "typescript";

function fail(path: string, left: ts.Node, right: ts.Node): never {
  throw new Error(
    `ProofScript composition mismatch at ${path}: ${ts.SyntaxKind[left.kind]} !== ${ts.SyntaxKind[right.kind]}`,
  );
}

function compareNode(
  left: ts.Node | undefined,
  right: ts.Node | undefined,
  renames: Map<string, string>,
  path: string,
): void {
  if (left === undefined || right === undefined) {
    if (left === right) {
      return;
    }
    throw new Error(`ProofScript composition mismatch at ${path}: missing node`);
  }

  if (left.kind !== right.kind) {
    fail(path, left, right);
  }

  switch (left.kind) {
    case ts.SyntaxKind.Block: {
      const leftStatements = (left as ts.Block).statements;
      const rightStatements = (right as ts.Block).statements;
      if (leftStatements.length !== rightStatements.length) {
        throw new Error(`ProofScript composition mismatch at ${path}: statement count`);
      }
      for (let index = 0; index < leftStatements.length; index += 1) {
        compareNode(leftStatements[index], rightStatements[index], renames, `${path}.statements[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.ReturnStatement: {
      compareNode(
        (left as ts.ReturnStatement).expression,
        (right as ts.ReturnStatement).expression,
        renames,
        `${path}.return`,
      );
      return;
    }

    case ts.SyntaxKind.ThrowStatement: {
      compareNode(
        (left as ts.ThrowStatement).expression,
        (right as ts.ThrowStatement).expression,
        renames,
        `${path}.throw`,
      );
      return;
    }

    case ts.SyntaxKind.ExpressionStatement: {
      compareNode(
        (left as ts.ExpressionStatement).expression,
        (right as ts.ExpressionStatement).expression,
        renames,
        `${path}.expression`,
      );
      return;
    }

    case ts.SyntaxKind.VariableStatement: {
      compareNode(
        (left as ts.VariableStatement).declarationList,
        (right as ts.VariableStatement).declarationList,
        renames,
        `${path}.declarationList`,
      );
      return;
    }

    case ts.SyntaxKind.VariableDeclarationList: {
      const leftDeclarations = (left as ts.VariableDeclarationList).declarations;
      const rightDeclarations = (right as ts.VariableDeclarationList).declarations;
      if (leftDeclarations.length !== rightDeclarations.length) {
        throw new Error(`ProofScript composition mismatch at ${path}: declaration count`);
      }
      for (let index = 0; index < leftDeclarations.length; index += 1) {
        compareNode(
          leftDeclarations[index],
          rightDeclarations[index],
          renames,
          `${path}.declarations[${index}]`,
        );
      }
      return;
    }

    case ts.SyntaxKind.VariableDeclaration: {
      const leftDeclaration = left as ts.VariableDeclaration;
      const rightDeclaration = right as ts.VariableDeclaration;
      if (!ts.isIdentifier(leftDeclaration.name) || !ts.isIdentifier(rightDeclaration.name)) {
        throw new Error("ProofScript composition only supports identifier variable declarations");
      }
      renames.set(leftDeclaration.name.text, rightDeclaration.name.text);
      compareNode(leftDeclaration.initializer, rightDeclaration.initializer, renames, `${path}.initializer`);
      return;
    }

    case ts.SyntaxKind.IfStatement: {
      const leftIf = left as ts.IfStatement;
      const rightIf = right as ts.IfStatement;
      compareNode(leftIf.expression, rightIf.expression, renames, `${path}.condition`);
      compareNode(leftIf.thenStatement, rightIf.thenStatement, renames, `${path}.then`);
      compareNode(leftIf.elseStatement, rightIf.elseStatement, renames, `${path}.else`);
      return;
    }

    case ts.SyntaxKind.ForStatement: {
      const leftFor = left as ts.ForStatement;
      const rightFor = right as ts.ForStatement;
      compareNode(leftFor.initializer, rightFor.initializer, renames, `${path}.initializer`);
      compareNode(leftFor.condition, rightFor.condition, renames, `${path}.condition`);
      compareNode(leftFor.incrementor, rightFor.incrementor, renames, `${path}.incrementor`);
      compareNode(leftFor.statement, rightFor.statement, renames, `${path}.statement`);
      return;
    }

    case ts.SyntaxKind.BinaryExpression: {
      const leftBinary = left as ts.BinaryExpression;
      const rightBinary = right as ts.BinaryExpression;
      if (leftBinary.operatorToken.kind !== rightBinary.operatorToken.kind) {
        throw new Error(`ProofScript composition mismatch at ${path}: operator token`);
      }
      compareNode(leftBinary.left, rightBinary.left, renames, `${path}.left`);
      compareNode(leftBinary.right, rightBinary.right, renames, `${path}.right`);
      return;
    }

    case ts.SyntaxKind.CallExpression: {
      const leftCall = left as ts.CallExpression;
      const rightCall = right as ts.CallExpression;
      if (leftCall.arguments.length !== rightCall.arguments.length) {
        throw new Error(`ProofScript composition mismatch at ${path}: argument count`);
      }
      compareNode(leftCall.expression, rightCall.expression, renames, `${path}.callee`);
      for (let index = 0; index < leftCall.arguments.length; index += 1) {
        compareNode(leftCall.arguments[index], rightCall.arguments[index], renames, `${path}.args[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.NewExpression: {
      const leftNew = left as ts.NewExpression;
      const rightNew = right as ts.NewExpression;
      const leftArgs = leftNew.arguments ?? [];
      const rightArgs = rightNew.arguments ?? [];
      if (leftArgs.length !== rightArgs.length) {
        throw new Error(`ProofScript composition mismatch at ${path}: constructor argument count`);
      }
      compareNode(leftNew.expression, rightNew.expression, renames, `${path}.constructor`);
      for (let index = 0; index < leftArgs.length; index += 1) {
        compareNode(leftArgs[index], rightArgs[index], renames, `${path}.args[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.ConditionalExpression: {
      const leftConditional = left as ts.ConditionalExpression;
      const rightConditional = right as ts.ConditionalExpression;
      compareNode(leftConditional.condition, rightConditional.condition, renames, `${path}.condition`);
      compareNode(leftConditional.whenTrue, rightConditional.whenTrue, renames, `${path}.whenTrue`);
      compareNode(leftConditional.whenFalse, rightConditional.whenFalse, renames, `${path}.whenFalse`);
      return;
    }

    case ts.SyntaxKind.PropertyAccessExpression: {
      const leftAccess = left as ts.PropertyAccessExpression;
      const rightAccess = right as ts.PropertyAccessExpression;
      compareNode(leftAccess.expression, rightAccess.expression, renames, `${path}.object`);
      if (leftAccess.name.text !== rightAccess.name.text) {
        throw new Error(`ProofScript composition mismatch at ${path}: property name`);
      }
      return;
    }

    case ts.SyntaxKind.ElementAccessExpression: {
      const leftAccess = left as ts.ElementAccessExpression;
      const rightAccess = right as ts.ElementAccessExpression;
      compareNode(leftAccess.expression, rightAccess.expression, renames, `${path}.object`);
      compareNode(
        leftAccess.argumentExpression,
        rightAccess.argumentExpression,
        renames,
        `${path}.index`,
      );
      return;
    }

    case ts.SyntaxKind.ArrayLiteralExpression: {
      const leftArray = left as ts.ArrayLiteralExpression;
      const rightArray = right as ts.ArrayLiteralExpression;
      if (leftArray.elements.length !== rightArray.elements.length) {
        throw new Error(`ProofScript composition mismatch at ${path}: array element count`);
      }
      for (let index = 0; index < leftArray.elements.length; index += 1) {
        compareNode(leftArray.elements[index], rightArray.elements[index], renames, `${path}.elements[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.SpreadElement: {
      compareNode(
        (left as ts.SpreadElement).expression,
        (right as ts.SpreadElement).expression,
        renames,
        `${path}.spread`,
      );
      return;
    }

    case ts.SyntaxKind.ParenthesizedExpression: {
      compareNode(
        (left as ts.ParenthesizedExpression).expression,
        (right as ts.ParenthesizedExpression).expression,
        renames,
        `${path}.inner`,
      );
      return;
    }

    case ts.SyntaxKind.AsExpression: {
      compareNode(
        (left as ts.AsExpression).expression,
        (right as ts.AsExpression).expression,
        renames,
        `${path}.cast`,
      );
      return;
    }

    case ts.SyntaxKind.PostfixUnaryExpression: {
      const leftPostfix = left as ts.PostfixUnaryExpression;
      const rightPostfix = right as ts.PostfixUnaryExpression;
      if (leftPostfix.operator !== rightPostfix.operator) {
        throw new Error(`ProofScript composition mismatch at ${path}: postfix operator`);
      }
      compareNode(leftPostfix.operand, rightPostfix.operand, renames, `${path}.operand`);
      return;
    }

    case ts.SyntaxKind.PrefixUnaryExpression: {
      const leftPrefix = left as ts.PrefixUnaryExpression;
      const rightPrefix = right as ts.PrefixUnaryExpression;
      if (leftPrefix.operator !== rightPrefix.operator) {
        throw new Error(`ProofScript composition mismatch at ${path}: prefix operator`);
      }
      compareNode(leftPrefix.operand, rightPrefix.operand, renames, `${path}.operand`);
      return;
    }

    case ts.SyntaxKind.Identifier: {
      const leftIdentifier = left as ts.Identifier;
      const rightIdentifier = right as ts.Identifier;
      const expected = renames.get(leftIdentifier.text) ?? leftIdentifier.text;
      if (expected !== rightIdentifier.text) {
        throw new Error(
          `ProofScript composition mismatch at ${path}: expected identifier ${expected}, received ${rightIdentifier.text}`,
        );
      }
      return;
    }

    case ts.SyntaxKind.StringLiteral:
    case ts.SyntaxKind.NumericLiteral: {
      if ((left as ts.LiteralLikeNode).text !== (right as ts.LiteralLikeNode).text) {
        throw new Error(`ProofScript composition mismatch at ${path}: literal value`);
      }
      return;
    }

    case ts.SyntaxKind.TrueKeyword:
    case ts.SyntaxKind.FalseKeyword:
      return;

    default:
      throw new Error(`Unsupported node in ProofScript composition check: ${ts.SyntaxKind[left.kind]}`);
  }
}

export function assertEquivalentFunctions(
  implementation: ts.FunctionDeclaration,
  specification: ts.FunctionDeclaration,
  helperRenames: Map<string, string>,
): void {
  if (implementation.body === undefined || specification.body === undefined) {
    throw new Error("ProofScript composition requires function bodies");
  }
  if (implementation.parameters.length !== specification.parameters.length) {
    throw new Error("ProofScript composition requires matching parameter counts");
  }

  const renames = new Map(helperRenames);
  if (implementation.name !== undefined && specification.name !== undefined) {
    renames.set(implementation.name.text, specification.name.text);
  }

  for (let index = 0; index < implementation.parameters.length; index += 1) {
    const left = implementation.parameters[index];
    const right = specification.parameters[index];
    if (!ts.isIdentifier(left.name) || !ts.isIdentifier(right.name)) {
      throw new Error("ProofScript composition only supports identifier parameters");
    }
    renames.set(left.name.text, right.name.text);
  }

  compareNode(implementation.body, specification.body, renames, "body");
}

function collectHelperPairsNode(
  left: ts.Node | undefined,
  right: ts.Node | undefined,
  renames: Map<string, string>,
  pairs: Array<{ implementation: string; specification: string }>,
  path: string,
): void {
  if (left === undefined || right === undefined) {
    if (left === right) {
      return;
    }
    throw new Error(`ProofScript dependency inference mismatch at ${path}: missing node`);
  }

  if (left.kind !== right.kind) {
    return;
  }

  switch (left.kind) {
    case ts.SyntaxKind.Block: {
      const leftStatements = (left as ts.Block).statements;
      const rightStatements = (right as ts.Block).statements;
      if (leftStatements.length !== rightStatements.length) {
        return;
      }
      for (let index = 0; index < leftStatements.length; index += 1) {
        collectHelperPairsNode(
          leftStatements[index],
          rightStatements[index],
          renames,
          pairs,
          `${path}.statements[${index}]`,
        );
      }
      return;
    }

    case ts.SyntaxKind.ReturnStatement: {
      collectHelperPairsNode(
        (left as ts.ReturnStatement).expression,
        (right as ts.ReturnStatement).expression,
        renames,
        pairs,
        `${path}.return`,
      );
      return;
    }

    case ts.SyntaxKind.ThrowStatement: {
      collectHelperPairsNode(
        (left as ts.ThrowStatement).expression,
        (right as ts.ThrowStatement).expression,
        renames,
        pairs,
        `${path}.throw`,
      );
      return;
    }

    case ts.SyntaxKind.ExpressionStatement: {
      collectHelperPairsNode(
        (left as ts.ExpressionStatement).expression,
        (right as ts.ExpressionStatement).expression,
        renames,
        pairs,
        `${path}.expression`,
      );
      return;
    }

    case ts.SyntaxKind.VariableStatement: {
      collectHelperPairsNode(
        (left as ts.VariableStatement).declarationList,
        (right as ts.VariableStatement).declarationList,
        renames,
        pairs,
        `${path}.declarationList`,
      );
      return;
    }

    case ts.SyntaxKind.VariableDeclarationList: {
      const leftDeclarations = (left as ts.VariableDeclarationList).declarations;
      const rightDeclarations = (right as ts.VariableDeclarationList).declarations;
      if (leftDeclarations.length !== rightDeclarations.length) {
        return;
      }
      for (let index = 0; index < leftDeclarations.length; index += 1) {
        collectHelperPairsNode(
          leftDeclarations[index],
          rightDeclarations[index],
          renames,
          pairs,
          `${path}.declarations[${index}]`,
        );
      }
      return;
    }

    case ts.SyntaxKind.VariableDeclaration: {
      const leftDeclaration = left as ts.VariableDeclaration;
      const rightDeclaration = right as ts.VariableDeclaration;
      if (!ts.isIdentifier(leftDeclaration.name) || !ts.isIdentifier(rightDeclaration.name)) {
        return;
      }
      renames.set(leftDeclaration.name.text, rightDeclaration.name.text);
      collectHelperPairsNode(
        leftDeclaration.initializer,
        rightDeclaration.initializer,
        renames,
        pairs,
        `${path}.initializer`,
      );
      return;
    }

    case ts.SyntaxKind.IfStatement: {
      const leftIf = left as ts.IfStatement;
      const rightIf = right as ts.IfStatement;
      collectHelperPairsNode(leftIf.expression, rightIf.expression, renames, pairs, `${path}.condition`);
      collectHelperPairsNode(leftIf.thenStatement, rightIf.thenStatement, renames, pairs, `${path}.then`);
      collectHelperPairsNode(leftIf.elseStatement, rightIf.elseStatement, renames, pairs, `${path}.else`);
      return;
    }

    case ts.SyntaxKind.ForStatement: {
      const leftFor = left as ts.ForStatement;
      const rightFor = right as ts.ForStatement;
      collectHelperPairsNode(leftFor.initializer, rightFor.initializer, renames, pairs, `${path}.initializer`);
      collectHelperPairsNode(leftFor.condition, rightFor.condition, renames, pairs, `${path}.condition`);
      collectHelperPairsNode(leftFor.incrementor, rightFor.incrementor, renames, pairs, `${path}.incrementor`);
      collectHelperPairsNode(leftFor.statement, rightFor.statement, renames, pairs, `${path}.statement`);
      return;
    }

    case ts.SyntaxKind.BinaryExpression: {
      const leftBinary = left as ts.BinaryExpression;
      const rightBinary = right as ts.BinaryExpression;
      if (leftBinary.operatorToken.kind !== rightBinary.operatorToken.kind) {
        return;
      }
      collectHelperPairsNode(leftBinary.left, rightBinary.left, renames, pairs, `${path}.left`);
      collectHelperPairsNode(leftBinary.right, rightBinary.right, renames, pairs, `${path}.right`);
      return;
    }

    case ts.SyntaxKind.CallExpression: {
      const leftCall = left as ts.CallExpression;
      const rightCall = right as ts.CallExpression;
      if (leftCall.arguments.length !== rightCall.arguments.length) {
        return;
      }
      if (ts.isIdentifier(leftCall.expression) && ts.isIdentifier(rightCall.expression)) {
        const expected = renames.get(leftCall.expression.text) ?? leftCall.expression.text;
        if (expected !== rightCall.expression.text) {
          pairs.push({
            implementation: leftCall.expression.text,
            specification: rightCall.expression.text,
          });
        }
      } else {
        collectHelperPairsNode(leftCall.expression, rightCall.expression, renames, pairs, `${path}.callee`);
      }
      for (let index = 0; index < leftCall.arguments.length; index += 1) {
        collectHelperPairsNode(leftCall.arguments[index], rightCall.arguments[index], renames, pairs, `${path}.args[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.NewExpression: {
      const leftNew = left as ts.NewExpression;
      const rightNew = right as ts.NewExpression;
      const leftArgs = leftNew.arguments ?? [];
      const rightArgs = rightNew.arguments ?? [];
      if (leftArgs.length !== rightArgs.length) {
        return;
      }
      collectHelperPairsNode(leftNew.expression, rightNew.expression, renames, pairs, `${path}.constructor`);
      for (let index = 0; index < leftArgs.length; index += 1) {
        collectHelperPairsNode(leftArgs[index], rightArgs[index], renames, pairs, `${path}.args[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.ConditionalExpression: {
      const leftConditional = left as ts.ConditionalExpression;
      const rightConditional = right as ts.ConditionalExpression;
      collectHelperPairsNode(leftConditional.condition, rightConditional.condition, renames, pairs, `${path}.condition`);
      collectHelperPairsNode(leftConditional.whenTrue, rightConditional.whenTrue, renames, pairs, `${path}.whenTrue`);
      collectHelperPairsNode(leftConditional.whenFalse, rightConditional.whenFalse, renames, pairs, `${path}.whenFalse`);
      return;
    }

    case ts.SyntaxKind.PropertyAccessExpression: {
      const leftAccess = left as ts.PropertyAccessExpression;
      const rightAccess = right as ts.PropertyAccessExpression;
      collectHelperPairsNode(leftAccess.expression, rightAccess.expression, renames, pairs, `${path}.object`);
      if (leftAccess.name.text !== rightAccess.name.text) {
        return;
      }
      return;
    }

    case ts.SyntaxKind.ElementAccessExpression: {
      const leftAccess = left as ts.ElementAccessExpression;
      const rightAccess = right as ts.ElementAccessExpression;
      collectHelperPairsNode(leftAccess.expression, rightAccess.expression, renames, pairs, `${path}.object`);
      collectHelperPairsNode(leftAccess.argumentExpression, rightAccess.argumentExpression, renames, pairs, `${path}.index`);
      return;
    }

    case ts.SyntaxKind.ArrayLiteralExpression: {
      const leftArray = left as ts.ArrayLiteralExpression;
      const rightArray = right as ts.ArrayLiteralExpression;
      if (leftArray.elements.length !== rightArray.elements.length) {
        return;
      }
      for (let index = 0; index < leftArray.elements.length; index += 1) {
        collectHelperPairsNode(leftArray.elements[index], rightArray.elements[index], renames, pairs, `${path}.elements[${index}]`);
      }
      return;
    }

    case ts.SyntaxKind.AsExpression: {
      collectHelperPairsNode(
        (left as ts.AsExpression).expression,
        (right as ts.AsExpression).expression,
        renames,
        pairs,
        `${path}.cast`,
      );
      return;
    }

    case ts.SyntaxKind.SpreadElement: {
      collectHelperPairsNode(
        (left as ts.SpreadElement).expression,
        (right as ts.SpreadElement).expression,
        renames,
        pairs,
        `${path}.spread`,
      );
      return;
    }

    case ts.SyntaxKind.ParenthesizedExpression: {
      collectHelperPairsNode(
        (left as ts.ParenthesizedExpression).expression,
        (right as ts.ParenthesizedExpression).expression,
        renames,
        pairs,
        `${path}.inner`,
      );
      return;
    }

    case ts.SyntaxKind.PostfixUnaryExpression: {
      const leftPostfix = left as ts.PostfixUnaryExpression;
      const rightPostfix = right as ts.PostfixUnaryExpression;
      if (leftPostfix.operator !== rightPostfix.operator) {
        return;
      }
      collectHelperPairsNode(leftPostfix.operand, rightPostfix.operand, renames, pairs, `${path}.operand`);
      return;
    }

    case ts.SyntaxKind.PrefixUnaryExpression: {
      const leftPrefix = left as ts.PrefixUnaryExpression;
      const rightPrefix = right as ts.PrefixUnaryExpression;
      if (leftPrefix.operator !== rightPrefix.operator) {
        return;
      }
      collectHelperPairsNode(leftPrefix.operand, rightPrefix.operand, renames, pairs, `${path}.operand`);
      return;
    }

    case ts.SyntaxKind.Identifier: {
      const leftIdentifier = left as ts.Identifier;
      const rightIdentifier = right as ts.Identifier;
      const expected = renames.get(leftIdentifier.text) ?? leftIdentifier.text;
      if (expected !== rightIdentifier.text) {
        return;
      }
      return;
    }

    case ts.SyntaxKind.StringLiteral:
    case ts.SyntaxKind.NumericLiteral: {
      if ((left as ts.LiteralLikeNode).text !== (right as ts.LiteralLikeNode).text) {
        return;
      }
      return;
    }

    case ts.SyntaxKind.TrueKeyword:
    case ts.SyntaxKind.FalseKeyword:
      return;

    default:
      return;
  }
}

export function collectHelperCallPairs(
  implementation: ts.FunctionDeclaration,
  specification: ts.FunctionDeclaration,
): Array<{ implementation: string; specification: string }> {
  if (implementation.body === undefined || specification.body === undefined) {
    throw new Error("ProofScript dependency inference requires function bodies");
  }
  if (implementation.parameters.length !== specification.parameters.length) {
    throw new Error("ProofScript dependency inference requires matching parameter counts");
  }

  const renames = new Map<string, string>();
  if (implementation.name !== undefined && specification.name !== undefined) {
    renames.set(implementation.name.text, specification.name.text);
  }
  for (let index = 0; index < implementation.parameters.length; index += 1) {
    const left = implementation.parameters[index];
    const right = specification.parameters[index];
    if (!ts.isIdentifier(left.name) || !ts.isIdentifier(right.name)) {
      throw new Error("ProofScript dependency inference only supports identifier parameters");
    }
    renames.set(left.name.text, right.name.text);
  }

  const pairs: Array<{ implementation: string; specification: string }> = [];
  collectHelperPairsNode(implementation.body, specification.body, renames, pairs, "body");

  const deduped = new Map<string, { implementation: string; specification: string }>();
  for (const pair of pairs) {
    deduped.set(`${pair.implementation}=>${pair.specification}`, pair);
  }
  return [...deduped.values()];
}
