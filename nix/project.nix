# editorconfig-checker-disable-file
{ inputs, pkgs, lib, metatheory, r-with-packages, utils }:

let
  # Defines the Haskell project and its variants via haskell.nix.
  cabalProject = pkgs.haskell-nix.cabalProject' ({ config, pkgs, ... }:
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
        ghc912-profiled = {
          compiler-nix-name = "ghc912";
          modules = [{
            enableProfiling = true;
            enableLibraryProfiling = true;
          }];
        };
        ghc912.compiler-nix-name = "ghc912";
        ghc96-coverage.modules = [{
          packages.plutus-metatheory.doCoverage = true;
          packages.plutus-core.doCoverage = true;
          packages.plutus-core.configureFlags = [ "--ghc-option=-D__HPC_ENABLED__" ];
        }];
      };

      inputMap = { "https://chap.intersectmbo.org/" = inputs.CHaP; };

      sha256map = {
        # We need one of these for each source-repository-package stanza in cabal.project.
        "https://github.com/jaccokrijnen/plutus-cert"."e814b9171398cbdfecdc6823067156a7e9fc76a3" =
          "0srqvx0b819b5crrbsa9hz2fnr50ahqizvvm0wdmyq2bbpk2rka7";
        "https://github.com/snowleopard/alga"."d4e43fb42db05413459fb2df493361d5a666588a" =
          "0s1mlnl64wj7pkg3iipv5bb4syy3bhxwqzqv93zqlvkyfn64015i";
      };

      modules = [
        {
          packages = {
            plutus-executables.components.tests.test-certifier.build-tools =
              [ metatheory.agda-with-stdlib-and-metatheory ];

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

            plutus-core.configureFlags = [
              "--ghc-option=-D__GIT_REV__=\\\"${utils.getSourceInfoRev inputs}\\\""
              "--ghc-option=-D__GIT_COMMIT_DATE__=\\\"${utils.getSourceInfoLastModifiedDate inputs}\\\""
            ];

            plutus-cert.components.library.build-tools = [
              pkgs.perl
              pkgs.ocaml-ng.ocamlPackages_4_10.ocaml
              pkgs.ocaml-ng.ocamlPackages_4_10.ocamlbuild
              pkgs.ocaml-ng.ocamlPackages_4_10.findlib
              pkgs.coqPackages_8_13.coq
              pkgs.coqPackages_8_13.mathcomp
              pkgs.coqPackages_8_13.ExtLib
              pkgs.coqPackages_8_13.ssreflect
              pkgs.coqPackages_8_13.equations
            ];
          };
        }
        {
          packages = {
            docusaurus-examples.ghcOptions = [ "-Werror" ];
            cardano-constitution.ghcOptions = [ "-Werror" ];
            plutus-benchmark.ghcOptions = [ "-Werror" ];
            plutus-conformance.ghcOptions = [ "-Werror" ];
            plutus-core.ghcOptions = [ "-Werror" ];
            plutus-executables.ghcOptions = [ "-Werror" ];
            plutus-ledger-api.ghcOptions = [ "-Werror" ];
            plutus-metatheory.ghcOptions = [ "-Werror" ];
            plutus-tx.ghcOptions = [ "-Werror" ];
            plutus-tx-plugin.ghcOptions = [ "-Werror" ];
          };
        }
        {
          # Pass --no-create to every test suite that uses tasty-golden.
          # This causes tests to fail (rather than silently create) when a
          # golden file is missing, catching accidental omissions early.
          packages = {
            cardano-constitution.components.tests.cardano-constitution-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.bitwise-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.bls12-381-costs-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.cardano-loans-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.coop-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.ed25519-costs-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.linear-vesting-test.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.plutus-benchmark-lists-tests.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.plutus-benchmark-marlowe-tests.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.plutus-benchmark-nofib-tests.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.plutus-benchmark-script-contexts-tests.testFlags = [ "--no-create" ];
            plutus-benchmark.components.tests.validation-tests.testFlags = [ "--no-create" ];
            plutus-conformance.components.tests.agda-conformance.testFlags = [ "--no-create" ];
            plutus-conformance.components.tests.haskell-conformance.testFlags = [ "--no-create" ];
            plutus-conformance.components.tests.haskell-steppable-conformance.testFlags = [ "--no-create" ];
            plutus-core.components.tests.plutus-core-test.testFlags = [ "--no-create" ];
            plutus-core.components.tests.plutus-ir-test.testFlags = [ "--no-create" ];
            plutus-core.components.tests.untyped-plutus-core-test.testFlags = [ "--no-create" ];
            plutus-ledger-api.components.tests.plutus-ledger-api-plugin-test.testFlags = [ "--no-create" ];
            plutus-ledger-api.components.tests.plutus-ledger-api-test.testFlags = [ "--no-create" ];
            plutus-tx-plugin.components.tests.plutus-tx-plugin-tests.testFlags = [ "--no-create" ];
            plutus-tx-plugin.components.tests.size.testFlags = [ "--no-create" ];
            plutus-tx.components.tests.plutus-tx-test.testFlags = [ "--no-create" ];
          };
        }
        ({ lib, pkgs, ... }: lib.mkIf (pkgs.stdenv.hostPlatform.isWindows) {
          # This fixed basement compilation error on Windows (ref: https://ci.iog.io/build/8529222/nixlog/1)
          # ```
          # Preprocessing library for basement-0.0.16...
          # Size.hsc:126:30: error: initialization of ‘long long int’ from ‘void *’ makes integer from pointer without a cast []
          # compilation failed
          # ```
          packages.basement.configureFlags = [ "--hsc2hs-option=--cflag=-Wno-int-conversion" ];
        })
      ];
    });
in
cabalProject
