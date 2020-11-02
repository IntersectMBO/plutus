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
  sources = import ./sources.nix {}; 
  nixpkgs = sources.nixpkgs;
  rOverlay = self: super: {
    rPackages = super.rPackages.override {
      hexbin = super.rPackages.hexbin.overrideDerivation(attrs: {
        nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
        buildInputs = attrs.buildInputs ++ [ super.libiconv ];
      });
    };
  };
  pkgsForR = import nixpkgs {
    overlays = [ rOverlay ];
  };
  r-packages = with pkgsForR.rPackages; [pkgsForR.R tidyverse dplyr stringr MASS plotly];
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
      "https://github.com/input-output-hk/cardano-prelude"."71ea865408f2e03e6d6832359423546699730849" = "02v9bd95vjal7yp96b59dgap2k53c2lrg9vxw6d62cxzw8n635y6";
      "https://github.com/input-output-hk/cardano-base"."5035c9ed95e9d47f050314a7d96b1b2043288f61" = "103z0009sz586f2mvnmwl2hp9n94qy0n72ik521xhq7zmfwyv3m7";
      "https://github.com/raduom/cardano-ledger-specs"."2cac85306d8b3e07006e9081f36ce7ebf2d9d0a3" = "0w6z1va6a93f818m9byh49yxkkpd9q3xlxk5irpq3d42vmfpy447";
      "https://github.com/input-output-hk/iohk-monitoring-framework"."5c9627b6aee487f9b7ec44981aba57a6afc659b1" = "0ndnhff32h37xsc61b181m4vwaj4vm1z04p2rfwffnjjmgz23584";
      "https://github.com/input-output-hk/ouroboros-network"."75153affa23a0e68e035d7bb19880fe1ae35b1d4" = "0aj6rsqp93k2079bipv2ia7m56h2xwwlcjffr7mr99cz6l9xj96i";
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
            # Using https connections ultimately requires x509. But on
            # OSX, a pure build can't find the package. This is the
            # solution used by the wallet build, and we reuse it here.
            x509-system.components.library.preBuild = lib.optionalString (stdenv.isDarwin) ''
              substituteInPlace System/X509/MacOS.hs --replace security /usr/bin/security
            '';
            inline-r.package.ghcOptions = "-XStandaloneKindSignatures";
            # See https://github.com/input-output-hk/plutus/issues/1213
            marlowe.doHaddock = false;
            plutus-use-cases.doHaddock = false;
            plutus-ledger.doHaddock = false;
            plutus-benchmark.doHaddock = false;
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

            marlowe-actus.components.exes.marlowe-shiny = {
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
