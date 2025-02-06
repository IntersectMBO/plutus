# editorconfig-checker-disable-file
{ inputs, pkgs, lib, agda-with-stdlib, r-with-packages }:

let
  cabalProject = pkgs.haskell-nix.cabalProject' ({ config, pkgs, ... }: {
    name = "plutus";

    # We need the mkDefault here since compiler-nix-name will be overridden
    # in the flake variants.
    compiler-nix-name = lib.mkDefault "ghc96";

    src = ../.;

    flake.variants = {
      ghc96 = { }; # Alias for the default project
      profiled.modules = [{
        enableProfiling = true;
        enableLibraryProfiling = true;
      }];
      ghc810.compiler-nix-name = "ghc810";
      ghc98.compiler-nix-name = "ghc98";
      ghc910.compiler-nix-name = "ghc910";
    };

    inputMap = { "https://chap.intersectmbo.org/" = inputs.CHaP; };

    sha256map = {
      "https://github.com/jaccokrijnen/plutus-cert"."e814b9171398cbdfecdc6823067156a7e9fc76a3" =
        "0srqvx0b819b5crrbsa9hz2fnr50ahqizvvm0wdmyq2bbpk2rka7";
    };

    modules = [
      # Common
      {
        packages = {
          # plutus-metatheory needs agda with the stdlib around for the custom setup
          # I can't figure out a way to apply this as a blanket change for all the
          # components in the package, oh well
          plutus-metatheory.components.library.build-tools =
            [ agda-with-stdlib ];
          plutus-metatheory.components.exes.plc-agda.build-tools =
            [ agda-with-stdlib ];
          plutus-metatheory.components.tests.test-NEAT.build-tools =
            [ agda-with-stdlib ];

          plutus-executables.components.exes.uplc.build-tools =
            [ agda-with-stdlib ];

          plutus-executables.components.tests.test-simple.build-tools =
            [ agda-with-stdlib ];
          plutus-executables.components.tests.test-detailed.build-tools =
            [ agda-with-stdlib ];

          plutus-core.components.benchmarks.update-cost-model = {
            build-tools = [ r-with-packages ];
          };

          plutus-core.components.benchmarks.cost-model-test = {
            build-tools = [ r-with-packages ];
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
            with ocamlPkgs;
            with coqPkgs; [
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

          plutus-core.components.tests.plutus-core-test.postInstall = ''
            wrapProgram $out/bin/plutus-core-test --set PATH ${
              lib.makeBinPath [ pkgs.diffutils ]
            }
          '';

          plutus-core.components.tests.plutus-ir-test.postInstall = ''
            wrapProgram $out/bin/plutus-ir-test --set PATH ${
              lib.makeBinPath [ pkgs.diffutils ]
            }
          '';

          # We want to build it but not run the tests in CI.
          cardano-constitution.doCheck = false;
        };
      }

      # -Werror for CI
      # Only enable on the newer compilers. We don't care about warnings on the old ones,
      # and sometimes it's hard to be warning free on all compilers, e.g. the unused
      # packages warning is bad in 8.10.7
      # (https://gitlab.haskellib.org/ghc/ghc/-/merge_requests/6130)
      (lib.mkIf (config.compiler-nix-name != "ghc8107") {
        packages = {

          # Werror everything.
          # This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519
          plutus-benchmark.ghcOptions = [ "-Werror" ];
          plutus-executables.ghcOptions = [ "-Werror" ];
          plutus-conformance.ghcOptions = [ "-Werror" ];
          plutus-core.ghcOptions = [ "-Werror" ];
          plutus-ledger-api.ghcOptions = [ "-Werror" ];
          # FIXME: has warnings in generated code
          #plutus-metatheory.package.ghcOptions = "-Werror";
          plutus-tx.ghcOptions = [ "-Werror" ];
          plutus-tx-plugin.ghcOptions = [ "-Werror" ];
        };
      })
    ];
  });

in
cabalProject
