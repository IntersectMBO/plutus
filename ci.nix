# 'supportedSystems' restricts the set of systems that we will evaluate for. Useful when you're evaluting
# on a machine with e.g. no way to build the Darwin IFDs you need!
{ supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
}:
let
  inherit (import ./nix/dimension.nix) dimension;
  systems = nixpkgs: nixpkgs.lib.filterAttrs (_: v: builtins.elem v supportedSystems) {
    # I wanted to take these from 'lib.systems.examples', but apparently there isn't one for linux!
    linux = "x86_64-linux";
    darwin = "x86_64-darwin";
  };
  sources = import ./nix/sources.nix;
  # Useful for generic library functions: do not use for anything platform dependent
  genericPkgs = import sources.nixpkgs {};
in dimension "System" (systems genericPkgs) (systemName: system:
  let
    packageSet = import ./default.nix { inherit system; checkMaterialization = true; };
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
