x = 10;
y = new Number(7);

print(typeof x);
print(typeof y);

print(x + y);

Number.prototype.valueOf = function() { return 0 };
print(x + y);

print(y.toString());
print(x + y.toString());
print(x * y.toString());
