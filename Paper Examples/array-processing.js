function sum(arr) {
  var r = 0;
  for (var i = 0; i < arr["length"]; i = i + 1) {
    r = r + arr[i]; };
  return r };

print(sum([1, 2, 3]));
var a = [1, 2, 3, 4];
delete a["3"];
print(sum(a));
