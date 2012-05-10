Array.prototype.join = function (separator) {
  var l = this.length;  
  if (separator === undefined) separator = ",";
  separator = "" + separator;  
  if (l === 0) return "";
  var R = this[0];
  if (R === undefined || R === null)
    R = "";
  else
    R = ""+R;
  for (var k = 1; k < l; ++k) {
    var S = R + separator;
    var x = this[k];
    if (x === undefined || x === null) {
      R = S + "";
    }
    else
      R = S + (""+x);
  }
  return R;
};

Array.prototype.toLocaleString = function () {
  var l = this.length;
  var separator = ",";
  if (l === 0) return "";
  var R = this[0];
  if (R === undefined || R === null)
    R = "";
  else
    R = R.toLocaleString();
  for (var k = 1; k < l; ++k) {
    var S = R + separator;
    var x = this[k];
    if (x === undefined || x === null) {
      R = S + "";
    }
    else
      R = S + (x.toLocaleString());
  }
  return R;
};

// TODO: ES3 specifies quicksort!
Array.prototype.sort = function (comparefn) {
  var l = this.length;
  var sortCompare = function(x,y) {
    if (x === undefined && y === undefined) return 0;
    if (x === undefined) return 1;
    if (y === undefined) return -1;
    if (comparefn === undefined) {
      var xs = ""+x; var ys = ""+y;
      if (xs < ys) return -1;
      if (ys < xs) return 1;
      return 0;
    }
    return comparefn(x,y);
  };
 
  for (var i=0; i<l-1; i++) {
    //find the min and swarp it
    var min = i;
    for (var j=i+1; j<l; j++) {
      if (sortCompare(this[j],this[i]) < 0) min = j;
    } 
    var tmp = this[i];
    this[i] = this[min];
    this[min] = tmp;
  }
};
