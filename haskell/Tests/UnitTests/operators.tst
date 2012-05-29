//order of ops for postfix and prefix increment:
{
  var zoo = 40;
  result = zoo++;
  result += zoo*100
} :: 4140;

{
  var zoo = 40;
  result = ++zoo;
  result += zoo*100;
} :: 4141;

{
  var zoo = 40;
  result = zoo--;
  result += zoo*100;
} :: 3940;

{
  var zoo = 40;
  result = --zoo;
  result += zoo*100;
} :: 3939;

{
  var zoo = 40;
  result = zoo++ + ++zoo;
  result += zoo*100;
} :: 4282;

//op-in
{
  var o = {a: 20};
  var z = ('a' in o);
  result = z+"";
  result += ""+('q' in o);
} :: "truefalse";




