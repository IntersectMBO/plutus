function Data(c,xs) {
  this.constructor = c;
  this.args = xs;
}

Data.prototype.cases = function () {
  for (let i = 0; i < arguments.length; i += 2) {
    if (arguments[i] === this.constructor) {
      return arguments[i+1].apply(null, this.args);
    } else if (arguments[i] === "otherwise") {
      return arguments[i+1](this);
    }
  }
};

function show(x) {
  if (x instanceof Data) {
    return x.constructor + "(" + x.args.map(x => show(x)).join(",") + ")";
  } else if (x instanceof Array) {
    return "[" + x.map(x => show(x)).join(",") + "]";
  } else if (x instanceof String || typeof x == "string"){
    return JSON.stringify(x);
  } else {
    return x.toString();
  }
}

Data.Alts = function () {
  for (let i = 0; i < arguments.length; i++) {
    let c = arguments[i];
    
    window[c] = function () {
      return new Data(c,Array.prototype.slice.call(arguments));
    };
  }
}