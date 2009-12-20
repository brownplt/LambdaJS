{
  var x = 50;
  with ({ x : 10 }) { x = 30 }
  result = x;
} :: 50;


{
  var y = 50;
  with ({ x : 10 }) { y = 30 }
  result = y;
} :: 30;


{
  var x = 50;
  with ({ x : 10 }) { result = x }
} :: 10;


{
  var y = 50;
  with ({ zzz : 10 }) { result = y }
} :: 50;


{
  var x = 50000;
  with ({  x: 50, y : 30 }) {
    with ({ x: -50 }) { y = x; }
    result = x + y;
  }
} :: 0; 

{
  var x = 1;
  var o = {};
  with (o)
    x = o.x = 2;
  result = x + o.x;
} :: 4;

{
  (function() {
  var x = 1;
  var o = {};
  with (o)
    x = o.x = 2;
  result = x + o.x;
  })();
} :: 4;

{
  with (3) {
    var innards = 50;
  }
  result = innards;
} :: 50;