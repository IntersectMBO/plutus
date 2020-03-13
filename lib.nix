let
  # The Hackage index-state we use for things
  index-state = "2020-02-20T00:00:00Z";

  unfreePredicate = pkg:
      let unfreePkgs = [ "kindlegen" ]; in
      if pkg ? name then builtins.elem (builtins.parseDrvName pkg.name).name unfreePkgs
      else if pkg ? pname then builtins.elem pkg.pname unfreePkgs
      else false;

  comp = f: g: (v: f(g v));

in { inherit index-state unfreePredicate comp; }
