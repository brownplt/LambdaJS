//testing delete
{
  var z = 50;
  result = ""+z;
  result = result + (delete z);
  if (typeof z == "undefined") result += "deleted";
} :: "50truedeleted";

{
  var obj = {a: 10, b: 30, c: 40};
  result = "";
  result += (obj.c);
  result += (delete obj.c);
  result += (obj.c);
  result += (delete obj.nothere);
  result += (obj.nothere);
} :: "40trueundefinedtrueundefined";

