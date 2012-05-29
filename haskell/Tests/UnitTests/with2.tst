// Adapted from SpiderMonkey's test suite.
{
var a = 1;
var f = function () {return a;};
var obj = {a:2};
with (obj)  {
  result = f();
}
} :: 1;

{
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
  result = f();
}
} :: 2;

{
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
}
result = f()
} :: 2;

{
var a = 1;
var obj = {a:2, obj:{a:3}};
with (obj)
{
  with (obj)
  {
    var f = function () {return a;};
  }
}
result = f();
} :: 3;

// The test suite says:
//   "Like Section C, but here we actually delete obj before calling f.
//    We still expect 2 -"
// You cannot delete objects.  Objects are garbage collected.
{
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
}
delete obj;
result = f();
} :: 2;

{
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
}
delete obj;
var obj = {a:3};
with (obj)
{
  result = f(); // Lexical scope 101
}
} :: 2;

{ 
var self = this;
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
}
result = String([obj.hasOwnProperty('f'), self.hasOwnProperty('f')]);
} :: String([false, true]);

{
var self = this;
var a = 1;
var obj = {a:2};
with (obj)
{
  var f = function () {return a;};
}
result = String(['f' in obj, 'f' in self]);
} ::  String([false, true]);