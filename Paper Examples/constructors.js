function Point(x, y) {
  print(this.__proto__ === Point.prototype && x === 50 && y === 100);
  this.x = x;
  this.y = y };

pt = new Point(50, 100);

Point.prototype.getX = function() { return this.x }
print(pt.getX());

