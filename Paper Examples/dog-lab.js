var animal = { "length": 13, "width": 7 };
var dog = { "__proto__": animal, "barks": true };

print(dog["length"]);
print(dog["width"]);

var lab = { "__proto__": dog, "length": 2 };

print(lab["length"]);
print(lab["width"]);
print(lab["barks"]);

dog["width"] = 19;
print(dog["width"]);
print(animal["width"]);

print(lab["width"]);
