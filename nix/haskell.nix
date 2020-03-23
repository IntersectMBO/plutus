############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, pkgs
, haskell-nix
, buildPackages
, metatheory
}:

let
  pkgSet = haskell-nix.stackProject {
    # This is incredibly difficult to get right, almost everything goes wrong, see https://github.com/input-output-hk/haskell.nix/issues/496
    src = let root = ../.; in haskell-nix.haskellLib.cleanSourceWith {
      filter = pkgs.nix-gitignore.gitignoreFilter (pkgs.nix-gitignore.gitignoreCompileIgnore [../.gitignore] root) root;
      src =  root;
      # Otherwise this depends on the name in the parent directory, which reduces caching, and is
      # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
      name = "plutus";
    };
    # This turns the output into a fixed-output derivation, which speeds things
    # up, but means we need to invalidate this hash when we change stack.yaml.
    stack-sha256 = "1givi8mdzsv94lrav653am3zv6km14vmiysh6vwpr91xvzi7ci39";
    modules = [
        {
          # Borrowed from https://github.com/input-output-hk/haskell.nix/pull/427
          # This corresponds to the set of packages that comes with GHC. We are
          # here saying that we must get them from GHC itself, rather than trying
          # to "re-install" them into the package database.
          nonReinstallablePkgs =
            [ "rts" "ghc-heap" "ghc-prim" "integer-gmp" "integer-simple" "base"
              "deepseq" "array" "ghc-boot-th" "pretty" "template-haskell"
              "ghc-boot"
              "ghc" "Cabal" "Win32" "array" "binary" "bytestring" "containers"
              "directory" "filepath" "ghc-boot" "ghc-compact" "ghc-prim"
              "ghci" "haskeline"
              "hpc"
              "mtl" "parsec" "process" "text" "time" "transformers"
              "unix" "xhtml"
              "stm" "terminfo"
            ];

          # See https://github.com/input-output-hk/plutus/issues/1213
          packages.marlowe.doHaddock = false;
          packages.plutus-use-cases.doHaddock = false;
          packages.plutus-scb.doHaddock = false;
          packages.plutus-wallet-api.doHaddock = false;

          # Fix missing executables on the paths of the test runners. This is arguably
          # a bug, and the fix is a bit of a hack.
          packages.marlowe-hspec.components.tests.marlowe-hspec-test.preCheck = ''
            PATH=${lib.makeBinPath [ pkgs.z3 ]}:$PATH
          '';
          packages.marlowe-symbolic.components.tests.marlowe-symbolic-test.preCheck = ''
            PATH=${lib.makeBinPath [ pkgs.z3 ]}:$PATH
          '';
          # In this case we can just propagate the native dependencies for the build of the test executable,
          # which are actually set up right (we have a build-tool-depends on the executable we need)
          # I'm slightly surprised this works, hooray for laziness!
          packages.plc-agda.components.tests.test-plc-agda.preCheck = ''
            PATH=${lib.makeBinPath pkgSet.plc-agda.components.tests.test-plc-agda.executableToolDepends }:$PATH
          '';
          # FIXME: Somehow this is broken even with setting the path up as above
          packages.plc-agda.components.tests.test2-plc-agda.doCheck = false;

          # plc-agda is compiled from the Haskell source files generated from the Agda
          packages.plc-agda.src = "${metatheory.plutus-metatheory-compiled}/share/agda";
        }
     ];
    pkg-def-extras = [
      # Workaround for https://github.com/input-output-hk/haskell.nix/issues/214
      (hackage: {
        packages = {
          "hsc2hs" = (((hackage.hsc2hs)."0.68.4").revisions).default;
        };
      })
    ];
  };

in
  pkgSet
