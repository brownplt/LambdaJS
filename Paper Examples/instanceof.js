function Dog() { this.barks = "woof" };
function Cat() { this.purrs = "meow" };
dog = new Dog();
cat = new Cat();
print(dog.barks); // produces "woof"
print(cat.purrs); // produces "meow"

function animalThing(obj) {
  if (obj instanceof Cat) { return obj.purrs }
  else if (obj instanceof Dog) { return obj.barks }
  else { return "unknown animal" } };

print(animalThing(dog)); // returns "woof"
print(animalThing(cat)); // returns "meow" 
print(animalThing(4234)); // returns "unknown animal"

print(cat.__proto__ === Cat.prototype &&
      dog.__proto__ === Dog.prototype &&
      Cat.prototype !== Dog.prototype);


Cat.prototype = Dog.prototype;

print(cat.__proto__ !== Cat.prototype &&
      dog.__proto__ === Dog.prototype &&
      Cat.prototype === Dog.prototype);

print(animalThing(cat)); // returns "unknown animal"
print(animalThing(dog)) // returns undefined

