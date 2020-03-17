let
  inherit (import ./nix/dimension.nix) dimension;
  systems = {"x86_64-linux" = {}; "x86_64-darwin" = {};};
in dimension "System" systems (system: _:
  let
    packageSet = import ./default.nix { inherit system; };
    pkgs = packageSet.pkgs;
    lib = pkgs.lib;
    collectChecks = _: ps: pkgs.recurseIntoAttrs (builtins.mapAttrs (_: p: p.checks) ps);
    collectComponents = type: ps: packageSet.pkgs.haskell-nix.haskellLib.collectComponents' type ps;
  in
    dimension
      "Haskell component"
      {"library" = collectComponents; "tests" = collectComponents; "benchmarks" = collectComponents; "exes" = collectComponents; "checks" = collectChecks;}
      (type: selector: (selector type) packageSet.haskell.projectPackages)
    //
    {
      dev = pkgs.recurseIntoAttrs packageSet.dev.packages;
    }
    // lib.optionalAttrs (system == "x86_64-linux") {
      # Marlowe lambda builds with musl, and only on linux
      marlowe-symbolic-lambda = packageSet.marlowe-symbolic-lambda;
    })
