function foo() {
  if (true) { var x = 10 };
  return x};

print(foo()); // 10

function bar() { 
  x = 10;
  var x = x * x;
  return x }

print(bar()); // 100
x // error
