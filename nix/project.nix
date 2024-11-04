# editorconfig-checker-disable-file

{ repoRoot, inputs, pkgs, system, lib }:

let
  cabalProject = pkgs.haskell-nix.cabalProject' ({ config, pkgs, ... }:
    let isCrossCompiling = pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform; in
    {
      name = "plutus";

      # We need the mkDefault here since compiler-nix-name will be overridden
      # in the flake variants.
      compiler-nix-name = lib.mkDefault "ghc96";

      src = ../.;

      shell = {
        withHoogle = true;
        # We would expect R to be pulled in automatically as it's a dependency of
        # plutus-core, but it appears it is not, so we need to be explicit about
        # the dependency on R here. Adding it as a buildInput will ensure it's
        # added to the pkg-config env var.
        buildInputs = [ pkgs.R ];
      };

      flake.variants = {
        ghc96 = { }; # Alias for the default project
        ghc96-profiled.modules = [{
          enableProfiling = true;
          enableLibraryProfiling = true;
        }];
        ghc810.compiler-nix-name = "ghc810";
        ghc98.compiler-nix-name = "ghc98";
        ghc910.compiler-nix-name = "ghc910";
      };

      inputMap = { "https://chap.intersectmbo.org/" = inputs.iogx.inputs.CHaP; };

      sha256map = {
        "https://github.com/jaccokrijnen/plutus-cert"."e814b9171398cbdfecdc6823067156a7e9fc76a3" = "0srqvx0b819b5crrbsa9hz2fnr50ahqizvvm0wdmyq2bbpk2rka7";
      };

      modules = [

        (
          lib.mkIf (!isCrossCompiling) repoRoot.nix.agda.agda-project-module-patch
        )

        # Common
        {
          packages = {
            # plutus-metatheory needs agda with the stdlib around for the custom setup
            # I can't figure out a way to apply this as a blanket change for all the
            # components in the package, oh well
            plutus-metatheory.components.library.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];
            plutus-metatheory.components.exes.plc-agda.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];
            plutus-metatheory.components.tests.test-NEAT.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];

            plutus-executables.components.exes.uplc.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];
            plutus-executables.components.exes.uplc.postInstall = ''
              wrapProgram $out/bin/uplc ${repoRoot.nix.agda.wrap-program-args}
            '';

            plutus-executables.components.tests.test-simple.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];
            plutus-executables.components.tests.test-detailed.build-tools = [ repoRoot.nix.agda.agda-with-stdlib ];

            plutus-core.components.benchmarks.update-cost-model = {
              build-tools = [ repoRoot.nix.r-with-packages ];
            };

            plutus-core.components.benchmarks.cost-model-test = {
              build-tools = [ repoRoot.nix.r-with-packages ];
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

            plutus-core.components.tests.plutus-core-test.postInstall = ''
              wrapProgram $out/bin/plutus-core-test --set PATH ${lib.makeBinPath [ pkgs.diffutils ]}
            '';

            plutus-core.components.tests.plutus-ir-test.postInstall = ''
              wrapProgram $out/bin/plutus-ir-test --set PATH ${lib.makeBinPath [ pkgs.diffutils ]}
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


  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    shellArgs = repoRoot.nix.shell;
  };

in

project
