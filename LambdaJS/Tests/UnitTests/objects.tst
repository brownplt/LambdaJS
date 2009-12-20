//constructors
//new should be able to return an object and have that be used instead:
{
  function x() {
     this.x = "50";
     return {hey: "100"};
  }
  result = "" + (new x()).hey + "|" + (new x()).x;
} :: "100|undefined";

//should be able to have .prototype not be an object
//but should still be able to create objects
{
 function badprot() {}
 badprot.prototype = 100;
 var bo = new badprot();
 result = "" + (typeof badprot.prototype);
 result += ""+bo.waffle;
} :: "numberundefined";

{
 function z() {}
 result = "" + z.prototype.toString();
} :: "[object Object]";

//instanceof should go up the prototype chain
{
 function C() {};
 C.prototype = new String();
 var x = new C();
 result = ("" + (x instanceof Object)) + (x instanceof String);
} :: "truetrue";

//old created objects maintain the old prototype
{
  function C() {}
  var x = new C();
  C.prototype = new String();
 result = ("" + (x instanceof Object)) + (x instanceof String);
} :: "truefalse";