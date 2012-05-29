//catch should introduce a new variable to its own scope:
{
 result = "";
 function func() {
  var e = 300;
  try {
     throw "NOT 300";
  }
  catch (e) {
     result += ""+e;
  }
  result += "|"+e;
 }
 func();
} :: "NOT 300|300";

