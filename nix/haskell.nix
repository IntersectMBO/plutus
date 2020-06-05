############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, pkgs
, haskell-nix
, buildPackages
, metatheory
, checkMaterialization
}:

let
  project = haskell-nix.stackProject' {
    # This is incredibly difficult to get right, almost everything goes wrong, see https://github.com/input-output-hk/haskell.nix/issues/496
    src = let root = ../.; in haskell-nix.haskellLib.cleanSourceWith {
      filter = pkgs.nix-gitignore.gitignoreFilter (pkgs.nix-gitignore.gitignoreCompileIgnore [../.gitignore] root) root;
      src =  root;
      # Otherwise this depends on the name in the parent directory, which reduces caching, and is
      # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
      name = "plutus";
    };
    # These files need to be regenerated when you change the cabal files or stack resolver.
    # See ../CONTRIBUTING.doc for more information.
    materialized = ./stack.materialized;
    # If true, we check that the generated files are correct. Set in the CI so we don't make mistakes.
    inherit checkMaterialization;
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

          packages = {
            # See https://github.com/input-output-hk/plutus/issues/1213
            marlowe.doHaddock = false;
            plutus-use-cases.doHaddock = false;
            plutus-ledger.doHaddock = false;
            # FIXME: Haddock mysteriously gives a spurious missing-home-modules warning
            plutus-tx-plugin.doHaddock = false;

            # Fix missing executables on the paths of the test runners. This is arguably
            # a bug, and the fix is a bit of a hack.
            marlowe.components.tests.marlowe-test.preCheck = ''
              PATH=${lib.makeBinPath [ pkgs.z3 ]}:$PATH
            '';
            # In this case we can just propagate the native dependencies for the build of the test executable,
            # which are actually set up right (we have a build-tool-depends on the executable we need)
            # I'm slightly surprised this works, hooray for laziness!
            plc-agda.components.tests.test-plc-agda.preCheck = ''
              PATH=${lib.makeBinPath project.hsPkgs.plc-agda.components.tests.test-plc-agda.executableToolDepends }:$PATH
            '';
            # FIXME: Somehow this is broken even with setting the path up as above
            plc-agda.components.tests.test2-plc-agda.doCheck = false;

            # plc-agda is compiled from the Haskell source files generated from the Agda
            plc-agda.src = "${metatheory.plutus-metatheory-compiled}/share/agda";

            # Werror everything. This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519
            deployment-server.package.ghcOptions = "-Werror";
            iots-export.package.ghcOptions = "-Werror";
            language-plutus-core.package.ghcOptions = "-Werror";
            marlowe.package.ghcOptions = "-Werror";
            marlowe-symbolic.package.ghcOptions = "-Werror";
            marlowe-playground-server.package.ghcOptions = "-Werror";
            playground-common.package.ghcOptions = "-Werror";
            # FIXME: has warnings
            #plc-agda.package.ghcOptions = "-Werror";
            plutus-book.package.ghcOptions = "-Werror";
            plutus-contract.package.ghcOptions = "-Werror";
            plutus-ledger.package.ghcOptions = "-Werror";
            plutus-playground-server.package.ghcOptions = "-Werror";
            plutus-scb.package.ghcOptions = "-Werror";
            plutus-tx.package.ghcOptions = "-Werror";
            plutus-tx-plugin.package.ghcOptions = "-Werror";
            plutus-tutorial.package.ghcOptions = "-Werror";
            plutus-use-cases.package.ghcOptions = "-Werror";
          };
        }
     ];
  };

in
  project
