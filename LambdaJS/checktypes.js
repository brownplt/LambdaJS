function checkType(expr, subtypes) {
   return (subtypes.indexOf(expr["type"])) >= 0;
}


function isProgram(expr) {
   return checkType(expr, ["Program"]);
}


function isFunction(expr) {
   var subtypes = ["Function", "FunctionDeclaration", "FunctionExpression"];
   //return (subtypes.indexOf(expr["type"])) >= 0;
   return checkType(expr, subtypes);
}


function isExpression(expr) {
   var subtypes = [
      "Expression",
      "ThisExpression",
      "ArrayExpression",
      "ObjectExpression",
      "FunctionExpression",
      "SequenceExpression",
      "UnaryExpression",
      "BinaryExpression",
      "AssignmentExpression",
      "UpdateExpression",
      "LogicalExpression",
      "ConditionalExpression",
      "NewExpression",
      "CallExpression",
      "MemberExpression",
      "Identifier",
      "Literal",
      // Note: from here down are spidermonkey specific.  Not sure if needed
      "YieldExpression",
      "ComprehensionExpression",
      "GeneratorExpression",
      "GraphExpression",
      "GraphIndexExpression",
      "LetIndexExpression" ];
   return checkType(expr, subtypes);
}


function isThisExpression(expr) {
   return checkType(expr, ["ThisExpression"]);
}


function isArrayExpression(expr) {
   return checkType(expr, ["ArrayExpression"]);
}


function isObjectExpression(expr) {
   return checkType(expr, ["ObjectExpression"]);
}


function isFunctionExpression(expr) {
   return checkType(expr, ["FunctionExpression"]);
}


function isSequenceExpression(expr) {
   return checkType(expr, ["SequenceExpression"]);
}


function isUnaryExpression(expr) {
   return checkType(expr, ["UnaryExpression"]);
}


function isBinaryExpression(expr) {
   return checkType(expr, ["BinaryExpression"]);
}


function isAssignmentExpression(expr) {
   return checkType(expr, ["AssignmentExpression"]);
}


function isUpdateExpression(expr) {
   return checkType(expr, ["UpdateExpression"]);
}


function isLogicalExpression(expr) {
   return checkType(expr, ["LogicalExpression"]);
}


function isConditionalExpression(expr) {
   return checkType(expr, ["ConditionalExpression"]);
}


function isNewExpression(expr) {
   return checkType(expr, ["NewExpression"]);
}


function isCallExpression(expr) {
   return checkType(expr, ["CallExpression"]);
}


function isMemberExpression(expr) {
   return checkType(expr, ["MemberExpression"]);
}


// type check functions for spidermonkey-only expressions would go here //


function isStatement(expr) {
   var subtypes = [
      "Statement",
      "EmptyStatement",
      "BlockStatement",
      "ExpressionStatement",
      "IfStatement",
      "LabeledStatement",
      "BreakStatement",
      "ContinueStatement",
      "WithStatement",
      "SwitchStatement",
      "ReturnStatement",
      "ThrowStatement",
      "TryStatement",
      "WhileStatement",
      "DoWhileStatement",
      "ForStatement",
      "ForInStatement",
      "LetStatement",
      "DebuggerStatement" ];
   return checkType(expr, subtypes) || isDeclaration(expr);
}


function isEmptyStatement(expr) {
   return checkType(expr, ["EmptyStatement"]);
}


function isBlockStatement(expr) {
   return checkType(expr, ["BlockStatement"]);
}


function isExpressionStatement(expr) {
   return checkType(expr, ["ExpressionStatement"]);
}


function isIfStatement(expr) {
   return checkType(expr, ["IfStatement"]);
}


function isLabeledStatement(expr) {
   return checkType(expr, ["LabeledStatement"]);
}


function isBreakStatement(expr) {
   return checkType(expr, ["BreakStatement"]);
}


function isContinueStatement(expr) {
   return checkType(expr, ["ContinueStatement"]);
}


function isWithStatement(expr) {
   return checkType(expr, ["WithStatement"]);
}


function isSwitchStatement(expr) {
   return checkType(expr, ["SwitchStatement"]);
}


function isReturnStatement(expr) {
   return checkType(expr, ["ReturnStatement"]);
}


function isThrowStatement(expr) {
   return checkType(expr, ["ThrowStatement"]);
}


function isTryStatement(expr) {
   return checkType(expr, ["TryStatement"]);
}


function isWhileStatement(expr) {
   return checkType(expr, ["WhileStatement"]);
}


function isDoWhileStatement(expr) {
   return checkType(expr, ["DoWhileStatement"]);
}


function isForStatement(expr) {
   return checkType(expr, ["ForStatement"]);
}


function isForInStatement(expr) {
   return checkType(expr, ["ForInStatement"]);
}


function isDebuggerStatement(expr) {
   return checkType(expr, ["DebuggerStatement"]);
}


function isDeclaration(expr) {
   var subtypes = ["Declaration", "FunctionDeclaration", "VariableDeclaration"];
   return checkType(expr, subtypes);
}


function isFunctionDeclaration(expr) {
   return checkType(expr, ["FunctionDeclaration"]);
}


function isVariableDeclaration(expr) {
   return checkType(expr, ["VariableDeclaration"]);
}


function isPattern(expr) {
   var subtypes = ["Pattern", "ObjectPattern", "ArrayPattern", "Identifier"];
   return checkType(expr, subtypes);
}


function isObjectPattern(expr) {
   return checkType(expr, ["ObjectPattern"]);
}


function isArrayPattern(expr) {
   return checkType(expr, ["ArrayPattern"]);
}


function isSwitchCase(expr) {
   return checkType(expr, ["SwitchCase"]);
}


function isCatchClause(expr) {
   return checkType(expr, ["CatchClause"]);
}


function isComprehensionBlock(expr) {
   return checkType(expr, ["ComprehensionBlock"]);
}


function isIdentifier(expr) {
   return checkType(expr, ["Identifier"]);
}


function isLiteral(expr) {
   return checkType(expr, ["Literal"]);
}


function isUnaryOperator(expr) {
   return checkType(expr, ["UnaryOperator"]);
}


function isLogicalOperator(expr) {
   return checkType(expr, ["LogicalOperator"]);
}


function isAssignmentOperator(expr) {
   return checkType(expr, ["AssignmentOperator"]);
}


function isUpdateOperator(expr) {
   return checkType(expr, ["UpdateOperator"]);
}


function isBinaryOperator(expr) {
   return checkType(expr, ["BinaryOperator"]);
}
