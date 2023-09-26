# editorconfig-checker-disable-file 

{ repoRoot, inputs, lib, ... }:

let
  cabalProjectArgs = { config, pkgs, ... }: {

    name = "plutus";

    compiler-nix-name = lib.mkDefault "ghc92";

    src = ../.;

    # We would expect R to be pulled in automatically as it's a dependency of
    # plutus-core, but it appears it is not, so we need to be explicit about
    # the dependency on R here. Adding it as a buildInput will ensure it's
    # added to the pkg-config env var.
    shell = {
      withHoogle = false;
      buildInputs = [ pkgs.R ];
    };

    flake.variants = {
      ghc92 = { }; # Alias for the default project
      ghc92-profiled.modules = [{ enableProfiling = true; }];
      ghc810.compiler-nix-name = "ghc810";
      ghc96.compiler-nix-name = "ghc96";
    };

    inputMap = { "https://input-output-hk.github.io/cardano-haskell-packages" = inputs.CHaP; };

    # TODO: move this into the cabalib.project using the new conditional support?
    # Configuration settings needed for cabal configure to work when cross compiling.
    # We can't use `modules` for these as `modules` are only applied
    # after cabal has been configured.
    cabalProjectLocal = lib.optionalString (pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform)
      ''
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
      (lib.mkIf (pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform) {
        packages = {
          # Things that need plutus-tx-plugin
          plutus-benchmark.package.buildable = false;
          plutus-tx-plugin.package.buildable = false;
          # Needs agda
          plutus-metatheory.package.buildable = false;
          # These need R
          plutus-core.components.benchmarks.cost-model-test.buildable = false; # lib.mkForce false;
          plutus-core.components.exes.generate-cost-modelib.buildable = false; # lib.mkForce false;
          # This contains support for doing testing, so we're not interested in cross-compiling it
          plutus-conformance.package.buildable = false;
        };
      })
      {
        packages = {
          # Packages we just don't want docs for
          plutus-benchmark.doHaddock = false;

          # FIXME: Haddock mysteriously gives a spurious missing-home-modules warning
          plutus-tx-plugin.doHaddock = false;

          # In this case we can just propagate the native dependencies for the build of
          # the test executable, which are actually set up right (we have a
          # build-tool-depends on the executable we need)
          # I'm slightly surprised this works, hooray for laziness!
          plutus-metatheory.components.tests.test1.preCheck =
            let
              cmp = config.hsPkgs.plutus-metatheory.components.tests.test1;
              deps = cmp.executableToolDepends;
            in
            ''PATH=${lib.makeBinPath deps }:$PATH'';

          # FIXME: Somehow this is broken even with setting the path up as above
          plutus-metatheory.components.tests.test2.doCheck = false;

          # plutus-metatheory needs agda with the stdlib around for the custom setup
          # I can't figure out a way to apply this as a blanket change for all the
          # components in the package, oh well
          plutus-metatheory.components.library.build-tools = [ repoRoot.nix.agda-with-stdlib ];
          plutus-metatheory.components.exes.plc-agda.build-tools = [ repoRoot.nix.agda-with-stdlib ];
          plutus-metatheory.components.tests.test1.build-tools = [ repoRoot.nix.agda-with-stdlib ];
          plutus-metatheory.components.tests.test2.build-tools = [ repoRoot.nix.agda-with-stdlib ];
          plutus-metatheory.components.tests.test3.build-tools = [ repoRoot.nix.agda-with-stdlib ];

          plutus-core.components.benchmarks.update-cost-model = {
            build-tools = [ repoRoot.nix.r-with-packages ];
          };

          plutus-core.components.benchmarks.cost-model-test = {
            build-tools = [ repoRoot.nix.r-with-packages ];
          };
        };
      }
      (lib.mkIf (config.compiler-nix-name != "ghc8107") {
        packages = {
          # -Werror for CI
          # Only enable on the newer compilers. We don't care about warnings on the old ones,
          # and sometimes it's hard to be warning free on all compilers, e.g. the unused
          # packages warning is bad in 8.10.7
          # (https://gitlab.haskellib.org/ghc/ghc/-/merge_requests/6130)

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
  };


  project = lib.iogx.mkHaskellProject {
    inherit cabalProjectArgs;
    readTheDocs.siteFolder = "doc/read-the-docs-site";
    shellArgsForProjectVariant = repoRoot.nix.shell;
    combinedHaddock = {
      enable = true;
      prologue = ''
        = Combined documentation for all the public Plutus libraries

        == Handy module entrypoints

          * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
          * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
          * "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
          * "UntypedPlutusCore": On-chain Plutus code.
      '';
    };
  };

in

project
