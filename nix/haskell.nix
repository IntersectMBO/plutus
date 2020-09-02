############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, pkgs
, haskell-nix
, agdaPackages
, buildPackages
, checkMaterialization
}:

let
  r-packages = with pkgs.rPackages; [pkgs.R tidyverse dplyr stringr MASS];
  agdaWithStdlib = agdaPackages.agda.withPackages [ agdaPackages.standard-library ];
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
    sha256map = {
      "https://github.com/shmish111/purescript-bridge.git"."28c37771ef30b0d751960c061ef95627f05d290e" = "0n6q7g2w1xafngd3dwbbmfxfn018fmq61db7mymplbrww8ld1cp3";
      "https://github.com/shmish111/servant-purescript.git"."ece5d1dad16a5731ac22040075615803796c7c21" = "1axcbsaym64q67hvjc7b3izd48cgqwi734l7f7m22jpdc80li5f6";
      "https://github.com/input-output-hk/cardano-crypto.git"."2547ad1e80aeabca2899951601079408becbc92c" = "1p2kg2w02q5w1cvqzhfhqmxviy4xrzada3mmb096j2n6hfr20kri";
      "https://github.com/michaelpj/unlit.git"."9ca1112093c5ffd356fc99c7dafa080e686dd748" = "145sffn8gbdn6xp9q5b75yd3m46ql5bnc02arzmpfs6wgjslfhff";
      "https://github.com/raduom/ouroboros-network"."af744374a05d6a5eb76713b399595131e2a24c38" = "1fljr384bkyg0lj46bkgdplp9dzwkb9dz1r6j863niyvm3q50h66";
      "https://github.com/input-output-hk/cardano-prelude"."bd7eb69d27bfaee46d435bc1d2720520b1446426" = "1cmxh1gk7lvgs6bfr8v6k2lpjxmk0qam58clvdvxkybrlbh186ps";
      "https://github.com/input-output-hk/cardano-base"."5035c9ed95e9d47f050314a7d96b1b2043288f61" = "103z0009sz586f2mvnmwl2hp9n94qy0n72ik521xhq7zmfwyv3m7";
      "https://github.com/raduom/cardano-ledger-specs"."2cac85306d8b3e07006e9081f36ce7ebf2d9d0a3" = "0w6z1va6a93f818m9byh49yxkkpd9q3xlxk5irpq3d42vmfpy447";
      "https://github.com/raduom/iohk-monitoring-framework"."b5c035ad4e226d634242ad5979fa677921181435" = "19v32drfb7wy1yqpbxlqvgii0i7s2j89s05lqskx6855yn0calq4";
      "https://github.com/j-mueller/iohk-monitoring-framework"."636eb9f52f504e8009162b5cf7147e8acb727c1b" = "101ga1cp877b8qnksfanzyw6s4yglwf24mzwgh0pn1xs0l64h6j3";
      };
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
            plutus-metatheory.components.tests.test1.preCheck = ''
              PATH=${lib.makeBinPath project.hsPkgs.plutus-metatheory.components.tests.test1.executableToolDepends }:$PATH
            '';
            # FIXME: Somehow this is broken even with setting the path up as above
            plutus-metatheory.components.tests.test2.doCheck = false;

            # plutus-metatheory needs agda with the stdlib around for the custom setup
            # I can't figure out a way to apply this as a blanket change for all the components in the package, oh well
	    plutus-metatheory.components.library.build-tools = [ agdaWithStdlib ];
            plutus-metatheory.components.exes.plc-agda.build-tools = [ agdaWithStdlib ];
            plutus-metatheory.components.tests.test1.build-tools = [ agdaWithStdlib ];
            plutus-metatheory.components.tests.test2.build-tools = [ agdaWithStdlib ];
            plutus-metatheory.components.tests.test3.build-tools = [ agdaWithStdlib ];

            # Relies on cabal-doctest, just turn it off in the Nix build
            prettyprinter-configurable.components.tests.prettyprinter-configurable-doctest.buildable = lib.mkForce false;

            plutus-core.components.tests.plutus-core-test-cost-model = {
              build-tools = r-packages;
              # Seems to be broken on darwin for some reason
              platforms = lib.platforms.linux;
            };

            plutus-core.components.benchmarks.plutus-core-create-cost-model = {
              build-tools = r-packages;
              # Seems to be broken on darwin for some reason
              platforms = lib.platforms.linux;
            };

            # Broken due to warnings, unclear why the setting that fixes this for the build doesn't work here.
            iohk-monitoring.doHaddock = false;

            # Werror everything. This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519
            deployment-server.package.ghcOptions = "-Werror";
            iots-export.package.ghcOptions = "-Werror";
            plutus-core.package.ghcOptions = "-Werror";
            marlowe.package.ghcOptions = "-Werror";
            marlowe-symbolic.package.ghcOptions = "-Werror";
            marlowe-actus.package.ghcOptions = "-Werror";
            marlowe-playground-server.package.ghcOptions = "-Werror";
            playground-common.package.ghcOptions = "-Werror";
            # FIXME: has warnings
            #plutus-metatheory.package.ghcOptions = "-Werror";
            plutus-book.package.ghcOptions = "-Werror";
            plutus-contract.package.ghcOptions = "-Werror";
            plutus-ledger.package.ghcOptions = "-Werror";
            plutus-playground-server.package.ghcOptions = "-Werror";
            plutus-scb.package.ghcOptions = "-Werror";
            plutus-tx.package.ghcOptions = "-Werror";
            plutus-tx-plugin.package.ghcOptions = "-Werror";
            plutus-doc.package.ghcOptions = "-Werror";
            plutus-use-cases.package.ghcOptions = "-Werror";
          };
        }
     ];
  };

in
  project
