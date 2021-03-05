let
  unfreePredicate = pkg:
    let unfreePkgs = [ "kindlegen" ]; in
    if pkg ? name then builtins.elem (builtins.parseDrvName pkg.name).name unfreePkgs
    else if pkg ? pname then builtins.elem pkg.pname unfreePkgs
    else false;

in
{ inherit unfreePredicate; }
