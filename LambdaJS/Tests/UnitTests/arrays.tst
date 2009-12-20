{
  //basics:
  result = (["a", "b", "c"])[0];
} :: "a";
{
  result = (["a", "b", "c"])["1"];
} :: "b";
{
  result = (["a", "b", "c"])[1+1];
} :: "c";
{
  result = (["a", "b", "c"])[5];
} :: undefined;

{
  //arrays act like objects for non-uint indices
  a = [5,  9, 10];
  a.bob = 13;
  a["gas"] = 5;
  result = a["bob"] + a.gas;
} :: 18;

{
  //NON-UINT INDICES
  a = [1, 2, 3];
  a[84.2] = 5;
  a[-4] = 9;
  result = a.length;
} :: 3;

{
  //constructor should work too
  var z = new Array("1", "2", "3", "5");
  result = z.length + z[0] + z[1] + z[2] + z[3];
} :: "41235";

{
  var z = new Array();
  result = (z.length+"") + z[0];
} :: "0undefined";

{
  var z = new Array(300);
  result = z.length;
} :: 300;
  
{
  //non-constructor should behave the same
  var z = Array("1", "2", "3", "5");
  result = z.length + z[0] + z[1] + z[2] + z[3];
} :: "41235";

{
  var z = Array();
  result = (z.length+"") + z[0];
} :: "0undefined";

{
  var z = Array(300);
  result = z.length;
} :: 300;
  
{
  //setting a higher element extends the length
  var ary = [1, 2, 3];
  ary[10] = "HAHA";
  result = (ary.length);
} :: 11;

{
  //setting length to a low # deletes things:
  var ary = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
  ary.length = 2;
  result = ary[5];
} :: undefined;

//testing push
{
  var a = ["xom"];
  a.push(1);
  a.push("hey", "bye");
  result = "";
  result += a[0];
  result += a[1];
  result += a[2];
  result += a[3];
  result += a.length;
} :: "xom1heybye4";
//and pop
{
  var arry = ["a", "b", "c"];
  result = "";
  result += arry.pop();
  result += arry[0];
  result += arry[1];
  result += arry[2];
  result += arry.length;
} :: "cabundefined2";
{
  var arry = [];
  result = "";
  result += arry.pop();
  result += arry[0];
  result += arry.length;
} :: "undefinedundefined0";

{
  //array constructor working in every way
  var z = Array(1, 2, 3); 
  result = "" + (z[0] + z[1] + z[2]);
  z.blorka = Array;

  var f = new z.blorka(4, 5);
  result += ("" + (f[0] + f[1]));
  var g = z.blorka(6, 7);
  result += ("" + (g[0] + g[1]));
} :: "6913";