{
  # 'supportedSystems' restricts the set of systems that we will evaluate for. Useful when you're evaluting
  # on a machine with e.g. no way to build the Darwin IFDs you need!
  supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  # This will be used by the packages that get the git revision in lieu of actually trying to find it,
  # which doesn't work in all situations. Set to null to get it from git.
, rev ? "fake"
}:
let
  inherit (import ./nix/lib/ci.nix) dimension platformFilterGeneric filterAttrsOnlyRecursive filterSystems;
  sources = import ./nix/sources.nix;
  # limit supportedSystems to what the CI can actually build
  # currently that is linux and darwin.
  systems = filterSystems supportedSystems;

  # Collects haskell derivations and builds an attrset:
  #
  # { library = { ... }
  # , tests = { ... }
  # , benchmarks = { ... }
  # , exes = { ... }
  # , checks = { ... }
  # }
  #  Where each attribute contains an attribute set
  #  with all haskell components of that type
  mkHaskellDimension = pkgs: haskellProjects:
    let
      # retrieve all checks from a Haskell package
      collectChecks = _: ps: pkgs.haskell-nix.haskellLib.collectChecks' ps;
      # retrieve all components of a Haskell package
      collectComponents = type: ps: pkgs.haskell-nix.haskellLib.collectComponents' type ps;
      # Given a component type and the retrieve function, retrieve components from haskell packages
      select = type: selector: (selector type) haskellProjects;
      # { component-type : retriever-fn }
      attrs = {
        "library" = collectComponents;
        "tests" = collectComponents;
        "benchmarks" = collectComponents;
        "exes" = collectComponents;
        "checks" = collectChecks;
      };
    in
    dimension "Haskell component" attrs select;

  # Collects all project derivations to build grouped by system:
  #
  # { linux = { ... }
  # , darwin = { ... }
  # }
  mkSystemDimension = systems:
    let
      # given a system ("x86_64-linux") return an attrset of derivations to build
      select = _: system:
        let
          packages = import ./default.nix { inherit system rev; checkMaterialization = true; };
          pkgs = packages.pkgs;
          plutus = packages.plutus;
          isBuildable = platformFilterGeneric pkgs system;
        in
        filterAttrsOnlyRecursive (_: drv: isBuildable drv) {
          # build relevant top level attributes from default.nix
          inherit (packages) docs tests plutus-playground marlowe-playground plutus-scb marlowe-symbolic-lambda marlowe-playground-lambda plutus-playground-lambda;
          # The haskell.nix IFD roots for the Haskell project. We include these so they won't be GCd and will be in the
          # cache for users
          inherit (plutus.haskell.project) roots;
          # Should be in roots, see https://github.com/input-output-hk/haskell.nix/issues/967
          inherit (pkgs.haskell-nix) internal-nix-tools internal-cabal-install;

          # build the shell expression to be sure it works on all platforms
          shell = import ./shell.nix { inherit packages; };

          # build deployment tools
          inherit (plutus) thorp;

          # build all haskell packages and tests
          haskell = pkgs.recurseIntoAttrs (mkHaskellDimension pkgs plutus.haskell.projectPackages);
        };
    in
    dimension "System" systems select;
in
mkSystemDimension systems
