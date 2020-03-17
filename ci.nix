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
      # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
      metatheory = pkgs.recurseIntoAttrs {
        plc-agda = packageSet.haskell.packages.plc-agda.components.exes.plc-agda;
        test-plc-agda = packageSet.haskell.packages.plc-agda.components.tests.test-plc-agda;
        test2-plc-agda = packageSet.haskell.packages.plc-agda.components.tests.test2-plc-agda;
      };
    }
    // lib.optionalAttrs (system == "x86_64-linux") {
      # Marlowe lambda builds with musl, and only on linux
      marlowe-symbolic-lambda = packageSet.marlowe-symbolic-lambda;
    })
