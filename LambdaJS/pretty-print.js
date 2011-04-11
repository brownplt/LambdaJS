// TODO: hard coded relative paths are :(
load("checktypes.js");

function advanceIndent(indent) {
   return indent + "   ";
}


function printSourceLocation(l, indent) {
   print(indent + "(SourceLocation");
   var newTab = advanceIndent(indent);

   // Commenting this out because I'm not sure what to do with it
   //print(newTab + "Source");
   //print(advanceIndent(newTab) + l["source"]);

   print(newTab + "(Start");
   printPosition(l["start"], advanceIndent(newTab));
   print(newTab + ")");
   
   print(newTab + "(End");
   printPosition(l["end"], advanceIndent(newTab));
   print(newTab + ")");

   print(indent + ")");
}


function printPosition(p, indent) {
   print(indent + "(Position");
   var newTab = advanceIndent(indent);

   print(newTab + "(Line");
   print(advanceIndent(newTab) + p["line"]);
   print(newTab + ")");

   print(newTab + "(Column");
   print(advanceIndent(newTab) + p["column"]);
   print(newTab + ")");

   print(indent + ")");
}


/* Expression */
function printExpression(e, indent) {
   // Try subtypes first
   // TODO: all subtypes
   if (isThisExpression(e)) {
      printThisExpression(e, indent);
   } else if (isArrayExpression(e)) {
      printArrayExpression(e, indent);
   } else if (isObjectExpression(e)) {
      printObjectExpression(e, indent);
   } else if (isFunctionExpression(e)) {
      printFunctionExpression(e, indent);
   } else if (isSequenceExpression(e)) {
      printSequenceExpression(e, indent);
   } else if (isUnaryExpression(e)) {
      printUnaryExpression(e, indent);
   } else if (isBinaryExpression(e, indent)) {
      printBinaryExpression(e, indent);
   } else if (isAssignmentExpression(e)) {
      printAssignmentExpression(e, indent);
   } else if (isUpdateExpression(e)) {
      printUpdateExpression(e, indent);
   } else if (isLogicalExpression(e)) {
      printLogicalExpression(e, indent);
   } else if (isConditionalExpression(e)) {
      printConditionalExpression(e, indent);
   } else if (isNewExpression(e)) {
      printNewExpression(e, indent);
   } else if (isCallExpression(e)) {
      printCallExpression(e, indent);
   } else if (isMemberExpression(e)) {
      printMemberExpression(e, indent);
   } else if (isLiteral(e)) {
      printLiteral(e, indent);
   } else if (isIdentifier(e)) {
      printIdentifier(e, indent);
   // checks for spidermonkey-only expressions would go here //
   } else {
      throw "unknown expression type";
   }
}


function printThisExpression(e, indent) {
   print(indent + "(ThisExpression");
   var newTab = advanceIndent(indent);

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printArrayExpression(e, indent) {
   print(indent + "(ArrayExpression");

   var elements = e["elements"];
   var newTab = advanceIndent(indent);
   print(newTab + "(Elements");
   var innerTab = advanceIndent(newTab);
   for (elt in elements) {
      print(innerTab + "(Element");
      printExpression(elements[elt], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printObjectExpression(e, indent) {
   print(indent + "(ObjectExpression");
   var newTab = advanceIndent(indent);

   var properties = e["properties"];
   print(newTab + "(Properties");
   var innerTab = advanceIndent(newTab);
   for (p in properties) {
      printProperty(properties[p], innerTab);
   }
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printProperty(prop, indent) {
   print(indent + "(Property");

   var k = prop["key"];
   var newTab = advanceIndent(indent);

   print(newTab + "(Key");
   if (isLiteral(k)) {
      printLiteral(k, advanceIndent(newTab));
   } else if (isIdentifier(k)) {
      printIdentifier(k, advanceIndent(newTab));
   } else {
      throw "property with unknown key type";
   }
   print(newTab + ")");
   
   var value = prop["value"];
   print(newTab + "(Value");
   if (isPattern(value)) {
      printPattern(value, advanceIndent(newTab));
   } else {
      printExpression(value, advanceIndent(newTab));
   }
   print(newTab + ")");

   print(newTab + "(Kind");
   if (prop.hasOwnProperty("kind")) {
      print(advanceIndent(newTab) + prop["kind"]);
   } else {
      print(advanceIndent(newTab) + "none");
   }
   print(newTab + ")");

   print(indent + ")");
}


function printFunctionExpression(e, indent) {
   print(indent + "(FunctionExpression");
   var newTab = advanceIndent(indent);

   print(newTab + "(Id");
   if (e["id"] == null) {
      print(advanceIndent(newTab) + "null");
   } else {
      printIdentifier(e["id"], advanceIndent(newTab));
   }
   print(newTab + ")");

   print(newTab + "(Params");
   var params = e["params"];
   for (k in params) {
      var innerTab = advanceIndent(newTab);
      print(innerTab + "(Param");
      printPattern(params[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   var body = e["body"];
   print(newTab + "(Body");
   pretty_print(body, advanceIndent(newTab));
   print(newTab + ")");

   // TODO: do I need metadata (in e["meta"])?

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printSequenceExpression(e, indent) {
   print(indent + "(SequenceExpression");
   var newTab = advanceIndent(indent);

   var expressions = e["expressions"];
   print(newTab + "(Expressions");
   var innerTab = advanceIndent(newTab);
   for (k in expressions) {
      print(innerTab + "(Expression");
      printExpression(expressions[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);
   
   print(indent + ")");
}


function printUnaryExpression(e, indent) {
   print(indent + "(UnaryExpression");
   var newTab = advanceIndent(indent);

   /*
    * Note: the API docs are wrong.  There is no interface UnaryOperator <: Node
    * Or at least, it's not used here.  e["operator"] is just a string.
    */
   var operator = e["operator"];
   print(newTab + "(Operator");
   print(advanceIndent(newTab) + operator);
   print(newTab + ")");

   var prefix = e["prefix"];
   print(newTab + "(Prefix");
   print(advanceIndent(newTab) + prefix);
   print(newTab + ")");

   var argument = e["argument"];
   print(newTab + "(Argument");
   printExpression(argument, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printBinaryExpression(e, indent) {
   print(indent + "(BinaryExpression");
   var newTab = advanceIndent(indent);
   
   /*
    * Note: the API docs are wrong.  There is no interface BinaryOperator <: Node
    * Or at least, it's not used here.  e["operator"] is just a string.
    */
   var operator = e["operator"];
   print(newTab + "(Operator");
   print(advanceIndent(newTab) + operator);
   print(newTab + ")");

   var left = e["left"];
   print(newTab + "(Left");
   printExpression(left, advanceIndent(newTab));
   print(newTab + ")");

   var right = e["right"];
   print(newTab + "(Right");
   printExpression(right, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printAssignmentExpression(e, indent) {
   print(indent + "(AssignmentExpression");
   var newTab = advanceIndent(indent);
   
   /*
    * Note: the API docs are wrong.  There is no interface AssignmentOperator <: Node
    * Or at least, it's not used here.  e["operator"] is just a string.
    */
   var operator = e["operator"];
   print(newTab + "(Operator");
   print(advanceIndent(newTab) + operator);
   print(newTab + ")");

   /*
    * Note: The API docs wrongly say that left has type Expression.  It's possible
    * that left could be a Pattern in the case of "destructuring assignment
    * and binding forms". (Pattern is not a subtype of Expression).
    */

   var left = e["left"];
   print(newTab + "(Left");
   if (isPattern(left)) {
      printPattern(left, advanceIndent(newTab));
   } else if (isExpression(left)) {
      printExpression(left, advanceIndent(newTab));
   } else {
      throw "printAssignmentExpression: unknown type for 'left'";
   }
   print(newTab + ")");

   var right = e["right"];
   print(newTab + "(Right");
   printExpression(right, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printUpdateExpression(e, indent) {
   print(indent + "(UpdateExpression");
   var newTab = advanceIndent(indent);

   // Again with the *Operator crap
   var operator = e["operator"];
   print(newTab + "(Operator");
   print(advanceIndent(newTab) + operator);
   print(newTab + ")");

   var argument = e["argument"];
   print(newTab + "(Argument");
   printExpression(argument, advanceIndent(newTab));
   print(newTab + ")");

   var prefix = e["prefix"];
   print(newTab + "(Prefix");
   print(advanceIndent(newTab) + prefix);
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printLogicalExpression(e, indent) {
   print(indent + "(LogicalExpression");
   var newTab = advanceIndent(indent);
   
   /*
    * Note: the API docs are wrong.  There is no interface LogicalOperator <: Node
    * Or at least, it's not used here.  e["operator"] is just a string.
    */
   var operator = e["operator"];
   print(newTab + "(Operator");
   print(advanceIndent(newTab) + operator);
   print(newTab + ")");

   var left = e["left"];
   print(newTab + "(Left");
   printExpression(left, advanceIndent(newTab));
   print(newTab + ")");

   var right = e["right"];
   print(newTab + "(Right");
   printExpression(right, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printConditionalExpression(e, indent) {
   print(indent + "(ConditionalExpression");
   var newTab = advanceIndent(indent);

   var test = e["test"];
   print(newTab + "(Test");
   printExpression(test, advanceIndent(newTab));
   print(newTab + ")");

   var alternate = e["alternate"];
   print(newTab + "(Alternate");
   printExpression(alternate, advanceIndent(newTab));
   print(newTab + ")");

   var consequent = e["consequent"];
   print(newTab + "(Consequent");
   printExpression(consequent, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printNewExpression(e, indent) {
   print(indent + "(NewExpression");
   var newTab = advanceIndent(indent);
  
   /*
    * Note: API docs say e has a property "constructor"
    * It doesn't appear to have this...instead it's "callee"
    */
   var callee = e["callee"];
   print(newTab + "(Callee");
   printExpression(callee, advanceIndent(newTab));
   print(newTab + ")");

   var args = e["arguments"];
   print(newTab + "(Arguments");
   if (args == null) {
      print(advanceIndent(newTab) + args);
   } else {
      var innerTab = advanceIndent(newTab);
      for (a in args) {
         print(innerTab + "(Argument");
         printExpression(args[a], advanceIndent(innerTab));
         print(innerTab + ")");
      }
   }
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printCallExpression(e, indent) {
   print(indent + "(CallExpression");
   var newTab = advanceIndent(indent);

   var callee = e["callee"];
   print(newTab + "(Callee");
   printExpression(callee, advanceIndent(newTab));
   print(newTab + ")");

   var args = e["arguments"];
   var innerTab = advanceIndent(newTab);
   print(newTab + "(Arguments");
   for (a in args) {
      print(innerTab + "(Argument");
      printExpression(args[a], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


function printMemberExpression(e, indent) {
   print(indent + "(MemberExpression");
   var newTab = advanceIndent(indent);

   var obj = e["object"];
   print(newTab + "(Object");
   printExpression(obj, advanceIndent(newTab));
   print(newTab + ")");

   var property = e["property"];
   print(newTab + "(Property");
   pretty_print(property, advanceIndent(newTab));
   print(newTab + ")");

   var computed = e["computed"];
   print(newTab + "(Computed");
   print(advanceIndent(newTab) + computed);
   print(newTab + ")");

   printSourceLocation(e["loc"], newTab);

   print(indent + ")");
}


// The print functions for spidermonkey-only expressions would go here //


/* Pattern */
function printPattern(p, indent) {
   if (isObjectPattern(p)) {
      printObjectPattern(p, indent);
   } else if (isArrayPattern(p, indent)) {
      printArrayPattern(p, indent);
   } else if (isIdentifier(p)) {
      printIdentifier(p, indent);
   } else {
      //print(indent + "Pattern");
      throw "unknown pattern type";
   }
}


function printObjectPattern(p, indent) {
   print(indent + "(ObjectPattern");
   var newTab = advanceIndent(indent);

   var properties = p["properties"];
   print(newTab + "(Properties");
   var innerTab = advanceIndent(newTab);
   for (k in properties) {
      print(innerTab + "(Property");
      printProperty(properties[k], advanceIndent(newTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(p["loc"], newTab);

   print(indent + ")");
}


function printArrayPattern(p, indent) {
   print(indent + "(ArrayPattern");
   var newTab = advanceIndent(indent);

   var elements = p["elements"];
   print(newTab + "(Elements");
   if (elements == null) {
      print(advanceIndent(newTab) + elements);
   } else {
      var innerTab = advanceIndent(newTab);
      for (k in elements) {
         print(innerTab + "(Element");
         printPattern(elements[k], advanceIndent(innerTab));
         print(innerTab + ")");
      }
   }
   print(newTab + ")");

   printSourceLocation(p["loc"], newTab);

   print(indent + ")");
}


// switchcase
function printSwitchCase(c, indent) {
   print(indent + "(SwitchCase");
   var newTab = advanceIndent(indent);

   var test = c["test"];
   print(newTab + "(Test");
   if (test == null) {
      print(advanceIndent(newTab) + test);
   } else {
      printExpression(test, advanceIndent(newTab));
   }
   print(newTab + ")");

   var consequent = c["consequent"];
   print(newTab + "(Consequents");
   var innerTab = advanceIndent(newTab);
   for (k in consequent) {
      print(innerTab + "(Consequent");
      printStatement(consequent[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(c["loc"], newTab);

   print(indent + ")");
}


function printCatchClause(c, indent) {
   print(indent + "(CatchClause");
   var newTab = advanceIndent(indent);

   var param = c["param"];
   print(newTab + "(Param");
   printPattern(param, advanceIndent(newTab));
   print(newTab + ")");

   // skipping spidermonkey-specific "guard"
   
   var body = c["body"];
   print(newTab + "(Body");
   printBlockStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(c["loc"], newTab);

   print(indent + ")");
}


function printIdentifier(p, indent) {
   print(indent + "(Identifier");
   var newTab = advanceIndent(indent);

   var name = p["name"];
   print(newTab + "(Name");
   print(advanceIndent(newTab) + name);
   print(newTab + ")");

   // The identifier object produced as part of a function object
   // doesn't have an associated source location.  See printFunction.
   if (p["loc"] != null) {
      printSourceLocation(p["loc"], newTab);
   }

   print(indent + ")");
}


function printLiteral(l, indent) {
   print(indent + "(Literal");
   var newTab = advanceIndent(indent);

   var value = l["value"];
   print(newTab + "(Value");
   print(advanceIndent(newTab) + value);
   print(newTab + ")");

   printSourceLocation(l["loc"], newTab);

   print(indent + ")");
}


/* Statement */
function printStatement(stmt, indent) {
   if (isEmptyStatement(stmt)) {
      printEmptyStatement(stmt, indent);
   } else if (isBlockStatement(stmt)) {
      printBlockStatement(stmt, indent);
   } else if (isExpressionStatement(stmt)) {
      printExpressionStatement(stmt, indent);
   } else if (isIfStatement(stmt)) {
      printIfStatement(stmt, indent);
   } else if (isLabeledStatement(stmt)) {
      printLabeledStatement(stmt, indent);
   } else if (isBreakStatement(stmt)) {
      printBreakStatement(stmt, indent);
   } else if (isContinueStatement(stmt)) {
      printContinueStatement(stmt, indent);
   } else if (isWithStatement(stmt)) {
      printWithStatement(stmt, indent);
   } else if (isSwitchStatement(stmt)) {
      printSwitchStatement(stmt, indent);
   } else if (isReturnStatement(stmt)) {
      printReturnStatement(stmt, indent);
   } else if (isThrowStatement(stmt)) {
      printThrowStatement(stmt, indent);
   } else if (isTryStatement(stmt)) {
      printTryStatement(stmt, indent);
   } else if (isWhileStatement(stmt)) {
      printWhileStatement(stmt, indent);
   } else if (isDoWhileStatement(stmt)) {
      printDoWhileStatement(stmt, indent);
   } else if (isForStatement(stmt)) {
      printForStatement(stmt, indent);
   } else if (isForInStatement(stmt)) {
      printForInStatement(stmt, indent);
   } else if (isDebuggerStatement(stmt)) {
      printDebuggerStatement(stmt, indent);
   } else if (isDeclaration(stmt)) {
      printDeclaration(stmt, indent);
   } else {
      throw "Unknown statement type";
   }
}


function printEmptyStatement(stmt, indent) {
   print(indent + "(EmptyStatement");

   printSourceLocation(stmt["loc"], advanceIndent(indent));

   print(indent + ")");
}


function printBlockStatement(stmt, indent) {
   print(indent + "(BlockStatement");
   var newTab = advanceIndent(indent);

   var statements = stmt["body"];
   print(newTab + "(Statements");
   var innerTab = advanceIndent(newTab);
   for (k in statements) {
      print(innerTab + "(Statement");
      printStatement(statements[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printExpressionStatement(stmt, indent) {
   print(indent + "(ExpressionStatement");
   var newTab = advanceIndent(indent);

   if (stmt.hasOwnProperty("expression") && stmt["expression"] != null) {
      print(newTab + "(Expression");
      printExpression(stmt["expression"], advanceIndent(newTab));
      print(newTab + ")");
   } else {
      throw "error: expression statement without expression";
   }

   printSourceLocation(stmt["loc"], advanceIndent(indent));

   print(indent + ")");
}


function printIfStatement(stmt, indent) {
   print(indent + "(IfStatement");
   var newTab = advanceIndent(indent);

   var testExp = stmt["test"];
   print(newTab + "(Test");
   printExpression(testExp, advanceIndent(newTab));
   print(newTab + ")");

   /*
    * Here's the documentation for if statements: 
    *
    *  interface IfStatement <: Statement {
    *     type: "IfStatement";
    *     test: Expression;
    *     alternate: Statement;
    *     consequent: Statement | null;
    *  }
    *
    *  It's wrong.  Alternate is the thing that could be null
    *  (if without matching else).  Consequent can't be null.
    */

   var consequent = stmt["consequent"];
   print(newTab + "(Consequent");
   printStatement(consequent, advanceIndent(newTab));
   print(newTab + ")");

   var alternate = stmt["alternate"];
   if (alternate != null) {
      print(newTab + "(Alternate");
      printStatement(alternate, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printLabeledStatement(stmt, indent) {
   print(indent + "(LabeledStatement");
   var newTab = advanceIndent(indent);

   var label = stmt["label"];
   print(newTab + "(Label");
   printIdentifier(label, advanceIndent(newTab));
   print(newTab + ")");

   var body = stmt["body"];
   print(newTab + "(Body");
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printBreakStatement(stmt, indent) {
   print(indent + "(BreakStatement");
   var newTab = advanceIndent(indent);

   var label = stmt["label"];
   if (label != null) {
      print(newTab + "(Label");
      printIdentifier(label, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printContinueStatement(stmt, indent) {
   print(indent + "(ContinueStatement");
   var newTab = advanceIndent(indent);

   var label = stmt["label"];
   if (label != null) {
      print(newTab + "(Label");
      printIdentifier(label, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printWithStatement(stmt, indent) {
   print(indent + "(WithStatement");
   var newTab = advanceIndent(indent);

   var obj = stmt["object"];
   print(newTab + "(Object");
   printExpression(obj, advanceIndent(newTab));
   print(newTab + ")");

   var body = stmt["body"];
   print(newTab + "(Body");
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printSwitchStatement(stmt, indent) {
   print(indent + "(SwitchStatement");
   var newTab = advanceIndent(indent);

   // Note: according to API docs, interface SwitchStatement has
   // property "test".  But in reality it's "discriminant".

   //var test = stmt["test"];
   var test = stmt["discriminant"];
   print(newTab + "(Discriminant");
   printExpression(test, advanceIndent(newTab));
   print(newTab + ")");

   var cases = stmt["cases"];
   print(newTab + "(Cases");
   var innerTab = advanceIndent(newTab);
   for (k in cases) {
      print(innerTab + "(Case");
      printSwitchCase(cases[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }  
   print(newTab + ")");

   // The lexical flag is metadata indicating whether the switch statement contains any 
   // un-nested let declarations (and therefore introduces a new lexical scope).
   var lexical = stmt["lexical"];
   print(newTab + "(Lexical");
   print(innerTab + lexical);
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printReturnStatement(stmt, indent) {
   print(indent + "(ReturnStatement");
   var newTab = advanceIndent(indent);

   var argument = stmt["argument"];
   if (argument != null) {
      print(newTab + "(Argument");
      printExpression(argument, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printThrowStatement(stmt, indent) {
   print(indent + "(ThrowStatement");
   var newTab = advanceIndent(indent);

   var argument = stmt["argument"];
   if (argument != null) {
      print(newTab + "(Argument");
      printExpression(argument, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printTryStatement(stmt, indent) {
   print(indent + "(TryStatement");
   var newTab = advanceIndent(indent);

   var block = stmt["block"];
   print(newTab + "(Block");
   printBlockStatement(block, advanceIndent(newTab));
   print(newTab + ")");

   var handler = stmt["handler"];
   // handler : CatchClause | [ CatchClause ] | null
   // but, multiple catch clauses only exists in spidermonkey
   if (handler instanceof Array) {
      print(newTab + "(Handlers");
      var innerTab = advanceTab(newTab);
      for (k in handler) {
         print(innerTab + "(Handler");
         printCatchClause(handler[k], advanceIndent(innerTab));
         print(innerTab + ")");
      }
      print(newTab + ")");
   } else if (handler instanceof Object) {
      print(newTab + "(Handler");
      printCatchClause(handler, advanceIndent(newTab));
      print(newTab + ")");
   }

   var finalizer = stmt["finalizer"];
   if (finalizer != null) {
      print(newTab + "(Finalizer");
      printBlockStatement(finalizer, advanceIndent(newTab));
      print(newTab + ")");
   }

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printWhileStatement(stmt, indent) {
   print(indent + "(WhileStatement");
   var newTab = advanceIndent(indent);

   var test = stmt["test"];
   print(newTab + "(Test");
   printExpression(test, advanceIndent(newTab));
   print(newTab + ")");

   var body = stmt["body"];
   print(newTab + "(Body");
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printDoWhileStatement(stmt, indent) {
   print(indent + "(DoWhileStatement");
   var newTab = advanceIndent(indent);

   var test = stmt["test"];
   print(newTab + "(Test");
   printExpression(test, advanceIndent(newTab));
   print(newTab + ")");

   var body = stmt["body"];
   print(newTab + "(Body");
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printForStatement(stmt, indent) {
   print(indent + "(ForStatement");
   var newTab = advanceIndent(indent);

   // init: VariableDeclaration | Expression | null
   var init = stmt["init"];
   print(newTab + "(Init");
   if (init == null) {
      print(advanceIndent(newTab) + init);
   } else if (init["type"] == "VariableDeclaration") {
      printVariableDeclaration(init, advanceIndent(newTab));
   } else {
      printExpression(init, advanceIndent(newTab));
   }
   print(newTab + "(");

   // test : Expression | null
   var test = stmt["test"];
   print(newTab + "(Test");
   if (test == null) {
      print(advanceIndent(newTab) + test);
   } else {
      printExpression(test, advanceIndent(newTab));
   }
   print(newTab + ")");

   // update : Expression | null
   var update = stmt["update"];
   print(newTab + "(Update");
   if (update == null) {
      print(advanceIndent(newTab) + update);
   } else {
      printExpression(update, advanceIndent(newTab));
   }
   print(newTab + ")");

   var body = stmt["body"];
   print(newTab + "(Body");
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


function printForInStatement(stmt, indent) {
   print(indent + "(ForInStatement");
   var newTab = advanceIndent(indent);

   // left : VariableDeclaration | Expression
   print(newTab + "(Left");
   var left = stmt["left"];
   if (left["type"] == "VariableDeclaration") {
      printVariableDeclaration(left, advanceIndent(newTab));
   } else {
      printExpression(left, advanceIndent(newTab));
   }
   print(newTab + ")");

   print(newTab + "(Right");
   var right = stmt["right"];
   printExpression(right, advanceIndent(newTab));
   print(newTab + ")");

   print(newTab + "(Statement");
   var body = stmt["body"];
   printStatement(body, advanceIndent(newTab));
   print(newTab + ")");

   printSourceLocation(stmt["loc"], newTab);

   print(indent + ")");
}


// omitting for-each statement and let statement (spidermonkey exclusive) //


function printDebuggerStatement(stmt, indent) {
   print(indent + "(DebuggerStatement)");
}


function printFunction(func, indent) {
   print(indent + "(Function");
   var newTab = advanceIndent(indent);

   /*
    * The identifier object at func["id"] (if it exists) doesn't have an associated
    * source location.  So I have to check for this in printIdentifier
    */
   print(newTab + "(Id");
   if (func["id"] == null) {
      print(advanceIndent(newTab) + "null");
   } else {
      printIdentifier(func["id"], advanceIndent(newTab));
   }
   print(newTab + ")");


   print(newTab + "(Params");
   var params = func["params"];
   for (k in params) {
      var innerTab = advanceIndent(newTab);
      print(innerTab + "(Param");
      printPattern(params[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   var body = func["body"];
   print(newTab + "(Body");
   pretty_print(body, advanceIndent(newTab)); // body could be a BlockStatement or Expression
   print(newTab + ")");

   printSourceLocation(func["loc"], newTab);

   print(indent + ")");
}


function printDeclaration(decl, indent) {
   if (isFunctionDeclaration(decl)) {
      printFunctionDeclaration(decl, indent);
   } else if (isVariableDeclaration(decl)) {
      printVariableDeclaration(decl, indent);
   } else {
      throw "unknown declaration type";
   }
}


function printFunctionDeclaration(decl, indent) {
   print(indent + "(FunctionDeclaration");
   var newTab = advanceIndent(indent);
   
   print(newTab + "(Id");
   printIdentifier(decl["id"], advanceIndent(newTab));
   print(newTab + ")");

   print(newTab + "(Params");
   var params = decl["params"];
   for (k in params) {
      var innerTab = advanceIndent(newTab);
      print(innerTab + "(Param");
      printPattern(params[k], advanceIndent(innerTab));
      print(innerTab + ")");
   }
   print(newTab + ")");

   var body = decl["body"];
   print(newTab + "(Body");
   pretty_print(body, advanceIndent(newTab));
   print(newTab + ")");

   // TODO: also has metadata: thunk, closed, generator, expression
   // do I need it?

   printSourceLocation(decl["loc"], newTab);

   print(indent + ")");
}


function printVariableDeclaration(decl, indent) {
   print(indent + "(VariableDeclaration");
   var newTab = advanceIndent(indent);

   var dList = decl["declarations"];
   print(newTab + "(Declarations");
   var innerTab = advanceIndent(newTab);
   for (d in dList) {
      printDeclarator(dList[d], innerTab);
   }
   print(newTab + ")");

   var kind = decl["kind"];
   print(newTab + "(Kind");
   print(advanceIndent(newTab) + kind);
   print(newTab + ")");

   printSourceLocation(decl["loc"], newTab);
   
   print(indent + ")");
}


function printDeclarator(d, indent) {
   print(indent + "(Declarator");
   var newTab = advanceIndent(indent);

   print(newTab + "(Id");
   if (d["id"] != null) {
      printPattern(d["id"], advanceIndent(newTab));
   } else {
      print(advanceIndent(newTab) + null);
   }
   print(newTab + ")");

   print(newTab + "(Init");
   if (d["init"] != null) {
      printExpression(d["init"], advanceIndent(newTab));
   } else {
      print(advanceIndent(newTab) + null);
   }
   print(newTab + ")");

   print(indent + ")");
}


// Note: I'm not sure UnaryOperator types actually exist, though they are
// mentioned in the API docs
function printUnaryOperator(op, indent) {
   print(indent + "UnaryOperator");
   var newTab = advanceIndent(indent);

   var token = op["token"];
   print(newTab + "Token");
   print(advanceIndent(newTab) + token);
}


function printProgram(p, indent) {
   print(indent + "(Program");
   var newTab = advanceIndent(indent);

   /*
    * Docs for Program: 
    *
    * interface Program <: Node {
    *    type: "Program";
    *    elements: [ Statement ];
    * }
    *
    * This is incorrect.  Should read: 
    *
    * interface Program <: Node {
    *    type: "Program";
    *    body: [ Statement ];
    * }
    */
   var body = p["body"];
   print(newTab + "(Body");
   for (b in body) {
      printStatement(body[b], advanceIndent(newTab));
   }
   print(newTab + ")");

   printSourceLocation(p["loc"], newTab);

   print(indent + ")");
}


function pretty_print(expr, indent) {
   // Expr is a Node
   var t = expr["type"];
   if (isProgram(expr)) {
      printProgram(expr, indent);
   } else if (isFunction(expr)) {
      printFunction(expr, indent);
   } else if (isExpression(expr)) {
      printExpression(expr, indent);
   } else if (isStatement(expr)) {
      printStatement(expr, indent);
   } else if (isPattern(expr)) {
      printPattern(expr, indent);
   } else if (isSwitchCase(expr)) {
      printSwitchCase(expr, indent);
   } else if (isCatchClause(expr)) {
      printCatchClause(expr, indent);
   } else if (isComprehensionBlock(expr)) {
      printComprehensionBlock(expr, indent);
   } else if (isIdentifier(expr)) {
      printIdentifier(expr, indent);
   } else if (isLiteral(expr)) {
      printLiteral(expr, indent);
   } else if (isUnaryOperator(expr)) {
      printUnaryOperator(expr, indent);
   } else if (isLogicalOperator(expr)) {
      printLogicalOperator(expr, indent);
   } else if (isAssignmentOperator(expr)) {
      printAssignmentOperator(expr, indent);
   } else if (isUpdateOperator(expr)) {
      printUpdateOperator(expr, indent);
   } else if (isBinaryOperator(expr)) {
      printBinaryOperator(expr, indent);
   } else {
      throw "Unknown Node Type";
   }
}


var f = read("input.js");
var expr = Reflect.parse(f, {loc : true});

try {
   pretty_print(expr, "");
} catch (err) {
   print(err);
}
