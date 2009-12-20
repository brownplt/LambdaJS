{
  //apply should return same result as calling the function.
  var z = Object.prototype.toString;
  var x = {};
  x.omg = z;
  result1 = x.omg(1, 2);
  result2 = z.apply(x, [1, 2]);
  result = result1 === result2;
} :: true;

//arguments should work
{
  result = "";
  ark = "";
  function double(x) { ark = (arguments[0]); return x*2; }
  result = "" + (double(4));
  result += ark;
} :: "84";

//arguments should work together with apply
{
  result = "";
  ark = "";
  function double(x) { ark = arguments[0]; return x*2; }
  result = "" + double.apply(null, [10]);
  result += ark;
} :: "2010";

//modifying arguments from one function does not modify it in the other
{
  function one() { two.apply(null, arguments); result = "" + (arguments[0]); }
  function two() { arguments[0] = 100; }

  one(40);
} :: "40";