function Data(c,xs) {
  return {
    constructor: c,
    args: xs
  };
}

Data.Alts = function () {
  for (let i = 0; i < arguments.length; i++) {
    let c = arguments[i];
    
    window[c] = function () {
      return new Data(c,Array.prototype.slice.call(arguments));
    };
  }
}

function cases(m, clauses) {
  let keys = Object.keys(clauses);
  for (let i = 0; i < keys.length; i++) {
    let k = keys[i];
    if (k === m.constructor) {
      return clauses[k].apply(null, m.args);
    } else if (k === "otherwise") {
      return clauses[k](m);
    }
  }
  /*
  for (let i = 0; i < arguments.length; i += 2) {
    if (arguments[i] === this.constructor) {
      return arguments[i+1].apply(null, this.args);
    } else if (arguments[i] === "otherwise") {
      return arguments[i+1](this);
    }
  }
  */
};

function show(x) {
  if (x.constructor && typeof x.constructor == "string" &&
       x.args && x.args instanceof Array) {
    return x.constructor + "(" + x.args.map(x => show(x)).join(",") + ")";
  } else if (x instanceof Array) {
    return "[" + x.map(x => show(x)).join(",") + "]";
  } else if (x instanceof String || typeof x == "string"){
    return JSON.stringify(x);
  } else if (x instanceof Function) {
    let names = x.toString().match(/^function \(([^\)]*)\)/)[1].split(",");
    let vars = names.map(x => ({ variable: true, name: x }));
    return "(" + names.join(",") + ") => " + show(x.apply(null, vars));
  } else if (x.variable) {
    return x.name;
  } else {
    return x.toString();
  }
}