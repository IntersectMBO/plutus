{ inputs, cell }:

{ compiler-nix-name ? cell.library.ghc-compiler-nix-name }:

let
  project = cell.library.haskell-nix.cabalProject' ({ pkgs, lib, ... }:
    let isCrossCompiling = pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform;
    in
    {

      inherit compiler-nix-name;

      # This is incredibly difficult to get right, almost everything goes wrong,
      # see https://github.com/input-output-hk/haskell.nix/issues/496
      src = cell.library.haskell-nix.haskellLib.cleanSourceWith {

        src = inputs.self.outPath;

        # Otherwise this depends on the name in the parent directory, which reduces caching, and is
        # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
        name = "plutus";
      };

      shell = {
        # We don't currently use this.
        withHoogle = false;

        # We would expect R to be pulled in automatically as it's a dependency of
        # plutus-core, but it appears it is not, so we need to be explicit about
        # the dependency on R here.  Adding it as a buildInput will ensure it's
        # added to the pkg-config env var.
        buildInputs = [ pkgs.R ];
      };

      inputMap = { "https://input-output-hk.github.io/cardano-haskell-packages" = inputs.CHaP; };
      sha256map = {
        "https://github.com/jaccokrijnen/plutus-cert"."e814b9171398cbdfecdc6823067156a7e9fc76a3" = "0srqvx0b819b5crrbsa9hz2fnr50ahqizvvm0wdmyq2bbpk2rka7"; # editorconfig-checker-disable-line
      };

      # TODO: move this into the cabal.project using the new conditional support?
      # Configuration settings needed for cabal configure to work when cross compiling.
      # We can't use `modules` for these as `modules` are only applied
      # after cabal has been configured.
      cabalProjectLocal = lib.optionalString isCrossCompiling ''
        -- When cross compiling we don't have a `ghc` package, so use
        -- the `plutus-ghc-stub` package instead.
        package plutus-tx-plugin
          flags: +use-ghc-stub

        -- Exclude tests that use `doctest`.  They will not work for
        -- cross compilation and `cabal` will not be able to make a plan.
        package prettyprinter-configurable
          tests: False
      '';

      modules = [

        # Cross compiling
        ({ pkgs, ... }: lib.mkIf isCrossCompiling {
          packages = {
            # Things that need plutus-tx-plugin
            plutus-benchmark.package.buildable = false;
            plutus-tx-plugin.package.buildable = false;
            # Needs agda
            plutus-metatheory.package.buildable = false;
            # These need R
            plutus-core.components.benchmarks.cost-model-test.buildable = lib.mkForce false;
            plutus-core.components.exes.generate-cost-model.buildable = lib.mkForce false;
            # This contains support for doing testing, so we're not interested in cross-compiling it
            plutus-conformance.package.buildable = false;
          };
        })

        # Common
        ({ pkgs, config, ... }: {
          packages = {
            # Packages we just don't want docs for
            plutus-benchmark.doHaddock = false;

            # FIXME: Haddock mysteriously gives a spurious missing-home-modules warning
            plutus-tx-plugin.doHaddock = false;

            # Something goes wrong with the custom setup
            # https://github.com/input-output-hk/haskell.nix/issues/2019
            prettyprinter-configurable.doHaddock = false;

            # In this case we can just propagate the native dependencies for the build of
            # the test executable, which are actually set up right (we have a
            # build-tool-depends on the executable we need)
            # I'm slightly surprised this works, hooray for laziness!
            plutus-metatheory.components.tests.test1.preCheck =
              let
                cmp = project.hsPkgs.plutus-metatheory.components.tests.test1;
                deps = cmp.executableToolDepends;
              in
              ''PATH=${lib.makeBinPath deps }:$PATH'';

            # FIXME: Somehow this is broken even with setting the path up as above
            plutus-metatheory.components.tests.test2.doCheck = false;

            # plutus-metatheory needs agda with the stdlib around for the custom setup
            # I can't figure out a way to apply this as a blanket change for all the
            # components in the package, oh well
            plutus-metatheory.components.library.build-tools = [ cell.packages.agda-with-stdlib ];
            plutus-metatheory.components.exes.plc-agda.build-tools = [ cell.packages.agda-with-stdlib ]; # editorconfig-checker-disable-line
            plutus-metatheory.components.tests.test1.build-tools = [ cell.packages.agda-with-stdlib ]; # editorconfig-checker-disable-line
            plutus-metatheory.components.tests.test2.build-tools = [ cell.packages.agda-with-stdlib ]; # editorconfig-checker-disable-line
            plutus-metatheory.components.tests.test3.build-tools = [ cell.packages.agda-with-stdlib ]; # editorconfig-checker-disable-line

            plutus-core.components.benchmarks.update-cost-model = {
              build-tools = [ cell.library.r-with-packages ];
            };

            plutus-core.components.benchmarks.cost-model-test = {
              build-tools = [ cell.library.r-with-packages ];
            };
            plutus-cert.components.library.build-tools =
              # Needs to build both itself and its bundled deps.
              # This needs both coq and ocaml packages, and only
              # works with particular versions. Fortunately
              # they're in nixpkgs.
              let
                ocamlPkgs = pkgs.ocaml-ng.ocamlPackages_4_10;
                coqPkgs = pkgs.coqPackages_8_13;
              in
              with ocamlPkgs; with coqPkgs; [
                pkgs.perl
                ocaml
                ocamlbuild
                findlib
                coq
                mathcomp
                coq-ext-lib
                ssreflect
                equations
              ];
          };
        })

        # -Werror for CI
        # Only enable on the newer compilers. We don't care about warnings on the old ones,
        # and sometimes it's hard to be warning free on all compilers, e.g. the unused
        # packages warning is bad in 8.10
        # (https://gitlab.haskell.org/ghc/ghc/-/merge_requests/6130)
        (lib.mkIf (compiler-nix-name != "ghc810") {
          packages = {
            # Werror everything.
            # This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519

            plutus-benchmark.ghcOptions = [ "-Werror" ];
            plutus-conformance.ghcOptions = [ "-Werror" ];
            plutus-core.ghcOptions = [ "-Werror" ];
            plutus-ledger-api.ghcOptions = [ "-Werror" ];
            # FIXME: has warnings in generated code
            #plutus-metatheory.package.ghcOptions = "-Werror";
            plutus-tx.ghcOptions = [ "-Werror" ];
            plutus-tx-plugin.ghcOptions = [ "-Werror" ];
            # This package's tests require doctest, which generates Haskell source
            # code. However, it does not add derivation strategies in said code,
            # which will fail the build with -Werror. Furthermore, barring an
            # upstream fix, there's nothing we can do about it other than
            # disabling -Werror on it.
            prettyprinter-configurable.ghcOptions = [ "-Werror" ];
          };
        })

      ];
    });
in
project

