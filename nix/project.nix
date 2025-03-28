# editorconfig-checker-disable-file
{ inputs, pkgs, lib, agda-with-stdlib, r-with-packages, utils }:

let
  cabalProject = pkgs.haskell-nix.cabalProject' ({ config, pkgs, ... }:
    let
      ghc-options-for-static-exe =
        lib.optionals pkgs.stdenv.hostPlatform.isMusl [ "-fexternal-interpreter" ];
    in
    {
      name = "plutus";

      # We need the mkDefault here since compiler-nix-name will be overridden
      # in flake.variants.
      compiler-nix-name = lib.mkDefault "ghc96";

      src = ../.;

      flake.variants = {
        ghc96 = { }; # Alias for the default project
        ghc96-profiled.modules = [{
          enableProfiling = true;
          enableLibraryProfiling = true;
        }];
        ghc96-coverage.modules = [{
          doCoverage = true;
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
        {
          packages = {

            plutus-metatheory.components.library.build-tools =
              [ agda-with-stdlib ];

            plutus-metatheory.components.exes.plc-agda.build-tools =
              [ agda-with-stdlib ];

            plutus-metatheory.components.tests.test-NEAT.build-tools =
              [ agda-with-stdlib ];

            plutus-executables.components.exes.pir = {
              preBuild = utils.exportGitHashAndGitCommitDateEnvVars inputs.self;
              ghcOptions = ghc-options-for-static-exe;
            };

            plutus-executables.components.exes.plc = {
              preBuild = utils.exportGitHashAndGitCommitDateEnvVars inputs.self;
              ghcOptions = ghc-options-for-static-exe;
            };

            plutus-executables.components.exes.uplc = {
              preBuild = utils.exportGitHashAndGitCommitDateEnvVars inputs.self;
              ghcOptions = ghc-options-for-static-exe;
              build-tools = [ agda-with-stdlib ];
            };

            plutus-executables.components.tests.test-simple.build-tools =
              [ agda-with-stdlib ];

            plutus-executables.components.tests.test-detailed.build-tools =
              [ agda-with-stdlib ];

            plutus-core.components.benchmarks.update-cost-model.build-tools =
              [ r-with-packages ];

            plutus-core.components.benchmarks.cost-model-test.build-tools =
              [ r-with-packages ];

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

            plutus-core.components.exes.plutus = {
              preBuild = utils.exportGitHashAndGitCommitDateEnvVars inputs.self;
              ghcOptions = ghc-options-for-static-exe;
            };

            plutus-cert.components.library.build-tools = [
              pkgs.perl
              pkgs.ocaml-ng.ocamlPackages_4_10.ocaml
              pkgs.ocaml-ng.ocamlPackages_4_10.ocamlbuild
              pkgs.ocaml-ng.ocamlPackages_4_10.findlib
              pkgs.coqPackages_8_13.coq
              pkgs.coqPackages_8_13.mathcomp
              pkgs.coqPackages_8_13.coq-ext-lib
              pkgs.coqPackages_8_13.ssreflect
              pkgs.coqPackages_8_13.equations
            ];
          };
        }

        {
          packages = {
            cardano-constitution.ghcOptions = [ "-Werror" ];
            plutus-benchmark.ghcOptions = [ "-Werror" ];
            plutus-conformance.ghcOptions = [ "-Werror" ];
            plutus-core.ghcOptions = [ "-Werror" ];
            plutus-executables.ghcOptions = [ "-Werror" ];
            plutus-ledger-api.ghcOptions = [ "-Werror" ];
            plutus-metatheory.ghcOptions = [ "-Werror" ];
            plutus-tx.ghcOptions = [ "-Werror" ];
            plutus-tx-plugin.ghcOptions = [ "-Werror" ];
            plutus-tx-test-util.ghcOptions = [ "-Werror" ];
          };
        }
      ];
    });
in
cabalProject
