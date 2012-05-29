{
    //do whatever you want, and store a value in 'result'
    //test will pass if result contains waht the
    //thing after :: desugars to
    result = 4 + 3;
} :: 7;

{ 
    result = ({toString:function(){return 4.0;}}) + 9.2;
} :: 13.2;

{ 
  result = { foo : 4545 }
} :: { foo : 4545 };

{
  //ensure to-string can modify 'this' things  
  var z = {toString: function() {
             this.x = 49;
             return "hey";
           }};
  var q = z+"";
  result = z.x;
} :: 49;

{
  //ensure prototype look-up works
  function Point() {
    this.x = 5;
  }
  Point.prototype = {y: 12};
  p = new Point();
  result = p.y;
} :: 12;

{
  //ensure ands work w/ tostring
  var z = {toString: function() {
             this.x = 49;
             return "hey";
           }};
  var q = (true && z) + "";
  result = z.x;
} :: 49;

{
  //check short circuiting
  var z = {toString: function() {
             this.x = 49;
             return "hey";
           }};
  var q = (false && z) + "";
  result = z.x;
} :: undefined;

{
  //ensure ands work w/ tostring
  var z = {valueOf: function() {
             this.x = 49;
             return "hey";
           }};
  var q = (true && z) + "";
  result = z.x;
} :: 49;

{
  //check short circuiting
  var z = {valueOf: function() {
             this.x = 49;
             return "hey";
           }};
  var q = (false && z) + "";
  result = z.x;
} :: undefined;
//order of operations for listexprs
{
  result = "";
  (result += "1", result += "2", result += "3");
} :: "123";
//complex lvalues work 
{
  result = "";
  var x = {y: 10};
  (result += "1", result += "2", result += "3", x).y = 13;
  result += "|" + x.y;
} :: "123|13";
{
  result = "";
  var x = {y: 10};
  (result += "1", result += "2", result += "3", x)['y'] = 13;
  result += "|" + x['y'];
} :: "123|13";
//lvalues are not evaluated twice with complex assign exprs
{
  var x = {y: 10};
  var y = 5;
  (y++, x).y += 5;
  result = "" + y + "|" + x.y;
} :: "6|15";
{
  var x = {y: 10};
  var y = 5;
  (y++, x)['y'] += 5;
  result = "" + y + "|" + x['y'];
} :: "6|15";


