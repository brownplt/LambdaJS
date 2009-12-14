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

