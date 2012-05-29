{
  //regular for loops iterating properly
  result = "";
  var z = 1;
  for (var i=0; i<z; i++) {
    result += "BHALAA";
  }
} :: "BHALAA";

{
  //make sure for-in woks.
  //this ensures general case and that $proto et.al. aren't enummed
  var z = {a: "hey"};
  result = "";
  for (var x in z) {
    result += x + ": " + z[x];
  }
} :: "a: hey";

{
  //test continue
  result = 0;
  var nums = {a: 50, b: 60, c: 70};
  for (var x in nums) {
    if (x == "b") continue;
    result += nums[x];
  }
} :: 120;

{
  //test break
  result = "didnt break";
  var nums = {a: 50, b: 60, c: 70};
  for (var x in nums) {
    if (x == "b") {
      break;
      result += "broked";
    }
  }
} :: "didnt break";