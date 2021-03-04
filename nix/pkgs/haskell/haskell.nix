############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, rPackages
, haskell-nix
, agdaWithStdlib
, buildPackages
, gitignore-nix
, z3
, R
, checkMaterialization
, compiler-nix-name
, enableHaskellProfiling
}:
let
  r-packages = with rPackages; [ R tidyverse dplyr stringr MASS plotly shiny shinyjs purrr ];
  project = haskell-nix.cabalProject' {
    inherit compiler-nix-name;
    # This is incredibly difficult to get right, almost everything goes wrong, see https://github.com/input-output-hk/haskell.nix/issues/496
    src = let root = ../../../.; in
      haskell-nix.haskellLib.cleanSourceWith {
        filter = gitignore-nix.gitignoreFilter root;
        src = root;
        # Otherwise this depends on the name in the parent directory, which reduces caching, and is
        # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
        name = "plutus";
      };
    # These files need to be regenerated when you change the cabal files.
    # See ../CONTRIBUTING.doc for more information.
    # Unfortuntely, they are *not* constant across all possible systems, so in some circumstances we need different sets of files
    # At the moment, we only need a different one for musl, but conceivably we might need one for darwin in future.
    # See https://github.com/input-output-hk/nix-tools/issues/97
    materialized =
      if stdenv.hostPlatform.isMusl then ./materialized-musl
      else if stdenv.hostPlatform.isUnix then ./materialized-unix
      else builtins.error "Don't have materialized files for this platform";
    # If true, we check that the generated files are correct. Set in the CI so we don't make mistakes.
    inherit checkMaterialization;
    sha256map = {
      "https://github.com/shmish111/purescript-bridge.git"."6a92d7853ea514be8b70bab5e72077bf5a510596" = "13j64vv116in3c204qsl1v0ajphac9fqvsjp7x3zzfr7n7g61drb";
      "https://github.com/shmish111/servant-purescript.git"."a76104490499aa72d40c2790d10e9383e0dbde63" = "11nxxmi5bw66va7psvrgrw7b7n85fvqgfp58yva99w3v9q3a50v9";
      "https://github.com/michaelpj/unlit.git"."9ca1112093c5ffd356fc99c7dafa080e686dd748" = "145sffn8gbdn6xp9q5b75yd3m46ql5bnc02arzmpfs6wgjslfhff";
      "https://github.com/input-output-hk/cardano-base"."4251c0bb6e4f443f00231d28f5f70d42876da055" = "02a61ymvx054pcdcgvg5qj9kpybiajg993nr22iqiya196jmgciv";
      "https://github.com/input-output-hk/cardano-crypto.git"."f73079303f663e028288f9f4a9e08bcca39a923e" = "1n87i15x54s0cjkh3nsxs4r1x016cdw1fypwmr68936n3xxsjn6q";
      "https://github.com/input-output-hk/cardano-ledger-specs"."097890495cbb0e8b62106bcd090a5721c3f4b36f" = "0i3y9n0rsyarvhfqzzzjccqnjgwb9fbmbs6b7vj40afjhimf5hcj";
      "https://github.com/input-output-hk/cardano-prelude"."ee4e7b547a991876e6b05ba542f4e62909f4a571" = "0dg6ihgrn5mgqp95c4f11l6kh9k3y75lwfqf47hdp554w7wyvaw6";
      "https://github.com/input-output-hk/goblins"."cde90a2b27f79187ca8310b6549331e59595e7ba" = "17c88rbva3iw82yg9srlxjv2ia5wjb9cyqw44hik565f5v9svnyg";
      "https://github.com/input-output-hk/iohk-monitoring-framework"."a89c38ed5825ba17ca79fddb85651007753d699d" = "0i4p3jbr9pxhklgbky2g7rfqhccvkqzph0ak5x8bb6kwp7c7b8wf";
      "https://github.com/input-output-hk/ouroboros-network"."6cb9052bde39472a0555d19ade8a42da63d3e904" = "0rz4acz15wda6yfc7nls6g94gcwg2an5zibv0irkxk297n76gkmg";
    };
    modules = [
      {
        reinstallableLibGhc = false;
        packages = {
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
            PATH=${lib.makeBinPath [ z3 ]}:$PATH
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

          plutus-core.components.benchmarks.update-cost-model = {
            build-tools = r-packages;
            # Seems to be broken on darwin for some reason
            platforms = lib.platforms.linux;
          };

          plutus-core.components.benchmarks.cost-model-test = {
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
          plutus-core.package.ghcOptions = "-Werror";
          marlowe.package.ghcOptions = "-Werror";
          marlowe-symbolic.package.ghcOptions = "-Werror";
          marlowe-actus.package.ghcOptions = "-Werror";
          marlowe-playground-server.package.ghcOptions = "-Werror";
          marlowe-dashboard-server.package.ghcOptions = "-Werror";
          playground-common.package.ghcOptions = "-Werror";
          # FIXME: has warnings
          #plutus-metatheory.package.ghcOptions = "-Werror";
          plutus-contract.package.ghcOptions = "-Werror";
          plutus-ledger.package.ghcOptions = "-Werror";
          plutus-ledger-api.package.ghcOptions = "-Werror";
          plutus-playground-server.package.ghcOptions = "-Werror";
          plutus-pab.package.ghcOptions = "-Werror";
          plutus-tx.package.ghcOptions = "-Werror";
          plutus-tx-plugin.package.ghcOptions = "-Werror";
          plutus-doc.package.ghcOptions = "-Werror";
          plutus-use-cases.package.ghcOptions = "-Werror";

          # External package settings

          # Using https connections ultimately requires x509. But on
          # OSX, a pure build can't find the package. This is the
          # solution used by the wallet build, and we reuse it here.
          x509-system.components.library.preBuild = lib.optionalString (stdenv.isDarwin) ''
            substituteInPlace System/X509/MacOS.hs --replace security /usr/bin/security
          '';
          inline-r.package.ghcOptions = "-XStandaloneKindSignatures";

          eventful-sql-common.package.ghcOptions = "-XDerivingStrategies -XStandaloneDeriving -XUndecidableInstances -XDataKinds -XFlexibleInstances -XMultiParamTypeClasses";
        };
      }
    ] ++ lib.optional enableHaskellProfiling {
      enableLibraryProfiling = true;
      enableExecutableProfiling = true;
    };
  };

in
project
