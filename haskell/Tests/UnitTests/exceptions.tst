{
  //if you can't convert an object to a primitive, that's a type error
  actual = "No error";
  try
  {
    var obj = {toString: function() {return new Object();}}
    obj == 'abc';
  }
  catch(e)
  {
    if (e instanceof TypeError)
      actual = "Pass";
    else
      actual = "Fail";
  }

  result = actual;
} :: "Pass";

{
  //apply expects arguments or array
  result = "No error";
  var x = function() {};
  try {
    x.apply(null, "HEY");
  }
  catch (e) {
    result = (e instanceof TypeError);
  }    
} :: true;