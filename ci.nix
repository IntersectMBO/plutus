let
  # TODO: make the system/attribute mapping nicer
  systemBuilds = system:
    let
      packageSet = import ./default.nix { inherit system; };
      pkgs = packageSet.pkgs;
      lib = pkgs.lib;
      collectComponents' = pkgs.haskell-nix.haskellLib.collectComponents';
    in pkgs.recurseIntoAttrs {
      libs = collectComponents' "library" packageSet.haskell.projectPackages;
      tests = collectComponents' "tests" packageSet.haskell.projectPackages;
      benchmarks = collectComponents' "benchmarks" packageSet.haskell.projectPackages;
      exes = collectComponents' "exes" packageSet.haskell.projectPackages;
      checks = pkgs.recurseIntoAttrs (builtins.mapAttrs (_: p: p.checks) packageSet.haskell.projectPackages);
      dev = pkgs.recurseIntoAttrs packageSet.dev.packages;
    } // (lib.optionalAttrs (system == linux) {
      # Marlowe lambda builds with musl, and only on linux
      marlowe-symbolic-lambda = packageSet.marlowe-symbolic-lambda;
      # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
      # Doesn't work on darwin
      metatheory = pkgs.recurseIntoAttrs {
        plc-agda = packageSet.haskell.packages.plc-agda.components.exes.plc-agda;
        test-plc-agda = packageSet.haskell.packages.plc-agda.components.tests.test-plc-agda;
        test2-plc-agda = packageSet.haskell.packages.plc-agda.components.tests.test2-plc-agda;
      };
    });
  linux = "x86_64-linux";
  darwin = "x86_64-darwin";
  # Darwin builds are not working on Hercules right now for some reason
  systems = [linux ];
in builtins.listToAttrs (builtins.map (system: { name = system; value = systemBuilds system; }) systems)
