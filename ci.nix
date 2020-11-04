# 'supportedSystems' restricts the set of systems that we will evaluate for. Useful when you're evaluting
# on a machine with e.g. no way to build the Darwin IFDs you need!
{ supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  # This will be used by the packages that get the git revision in lieu of actually trying to find it,
  # which doesn't work in all situations. Set to null to get it from git.
, rev ? "fake"
}:
let
  inherit (import ./nix/lib/ci.nix) dimension platformFilterGeneric filterAttrsOnlyRecursive;
  systems = nixpkgs: nixpkgs.lib.filterAttrs (_: v: builtins.elem v supportedSystems) {
    # I wanted to take these from 'lib.systems.examples', but apparently there isn't one for linux!
    linux = "x86_64-linux";
    darwin = "x86_64-darwin";
  };
  sources = import ./nix/sources.nix;
  # Useful for generic library functions: do not use for anything platform dependent
  genericPkgs = import sources.nixpkgs { };
in
dimension "System" (systems genericPkgs) (systemName: system:
  let
    packageSet = import ./default.nix { inherit system rev; checkMaterialization = true; };
    packages = import ./nix { inherit system rev; checkMaterialization = true; };
    pkgs = packages.pkgs;
    pkgsLocal = packages.pkgsLocal;
    lib = pkgs.lib;
    platformFilter = platformFilterGeneric pkgs system;
  in
  filterAttrsOnlyRecursive (_: v: platformFilter v) {
    inherit (packageSet) docs papers tests plutus-playground marlowe-playground plutus-scb marlowe-symbolic-lambda;
    inherit (pkgsLocal.haskell.project) roots;
    # build the shell expression to be sure it works on all platforms
    shell = import ./shell.nix { };
    haskell =
      let
        # These functions pull out from the Haskell package set either all the components of a particular type, or
        # all the checks.
        collectChecks = _: ps: pkgs.recurseIntoAttrs (builtins.mapAttrs (_: p: p.checks) ps);
        collectComponents = type: ps: pkgs.haskell-nix.haskellLib.collectComponents' type ps;
        # This computes the Haskell package set sliced by component type
      in
      pkgs.recurseIntoAttrs (dimension
        "Haskell component"
        { "library" = collectComponents; "tests" = collectComponents; "benchmarks" = collectComponents; "exes" = collectComponents; "checks" = collectChecks; }
        # Apply the selector to the Haskell package set
        (type: selector: (selector type) pkgsLocal.haskell.projectPackages));
  })
