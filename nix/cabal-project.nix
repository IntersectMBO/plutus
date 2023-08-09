# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#33-nixcabal-projectnix

{ nix, inputs, inputs', meta, config, l, pkgs, ... }:

let

  isCrossCompiling = pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform;


  isNotGhc8107 = meta.haskellCompiler != "ghc8107";


  # We would expect R to be pulled in automatically as it's a dependency of
  # plutus-core, but it appears it is not, so we need to be explicit about
  # the dependency on R here. Adding it as a buildInput will ensure it's
  # added to the pkg-config env var.
  shellBuildInputs = [ pkgs.R ];


  sha256map = {
    "https://github.com/tweag/HaskellR"."411d15fe5027494123e326c838955eff1c8e7ec8" = "0jax08z81xbfs3xz7zkk7x83cmr487iglifmxri205mf5bcj8ycj"; # editorconfig-checker-disable-line
  };


  # TODO: move this into the cabal.project using the new conditional support?
  # Configuration settings needed for cabal configure to work when cross compiling.
  # We can't use `modules` for these as `modules` are only applied
  # after cabal has been configured.
  cabalProjectLocal = l.optionalString isCrossCompiling ''
    -- When cross compiling we don't have a `ghc` package, so use
    -- the `plutus-ghc-stub` package instead.
    package plutus-tx-plugin
      flags: +use-ghc-stub

    -- Exclude tests that use `doctest`.  They will not work for
    -- cross compilation and `cabal` will not be able to make a plan.
    package prettyprinter-configurable
      tests: False
  '';

  packages = {

    # Things that need plutus-tx-plugin
    plutus-benchmark.package.buildable = !isCrossCompiling;
    plutus-tx-plugin.package.buildable = !isCrossCompiling;
    # Needs agda
    plutus-metatheory.package.buildable = !isCrossCompiling;
    # These need R
    plutus-core.components.benchmarks.cost-model-test.buildable = l.mkForce (!isCrossCompiling);
    plutus-core.components.exes.generate-cost-model.buildable = l.mkForce (!isCrossCompiling);
    # This contains support for doing testing, so we're not interested in cross-compiling it
    plutus-conformance.package.buildable = !isCrossCompiling;


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
      ''PATH=${l.makeBinPath deps }:$PATH'';

    # FIXME: Somehow this is broken even with setting the path up as above
    plutus-metatheory.components.tests.test2.doCheck = false;

    # plutus-metatheory needs agda with the stdlib around for the custom setup
    # I can't figure out a way to apply this as a blanket change for all the
    # components in the package, oh well
    plutus-metatheory.components.library.build-tools = [ nix.plutus.agda-with-stdlib ];
    plutus-metatheory.components.exes.plc-agda.build-tools = [ nix.plutus.agda-with-stdlib ]; # editorconfig-checker-disable-line
    plutus-metatheory.components.tests.test1.build-tools = [ nix.plutus.agda-with-stdlib ]; # editorconfig-checker-disable-line
    plutus-metatheory.components.tests.test2.build-tools = [ nix.plutus.agda-with-stdlib ]; # editorconfig-checker-disable-line
    plutus-metatheory.components.tests.test3.build-tools = [ nix.plutus.agda-with-stdlib ]; # editorconfig-checker-disable-line

    plutus-core.components.benchmarks.update-cost-model = {
      build-tools = [ nix.plutus.r-with-packages ];
    };

    plutus-core.components.benchmarks.cost-model-test = {
      build-tools = [ nix.plutus.r-with-packages ];
    };

    # -Werror for CI
    # Only enable on the newer compilers. We don't care about warnings on the old ones,
    # and sometimes it's hard to be warning free on all compilers, e.g. the unused
    # packages warning is bad in 8.10.7
    # (https://gitlab.haskell.org/ghc/ghc/-/merge_requests/6130)

    # Werror everything.
    # This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519

    plutus-benchmark.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    plutus-conformance.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    plutus-core.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    plutus-ledger-api.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    # FIXME: has warnings in generated code
    #plutus-metatheory.package.ghcOptions = "-Werror";
    plutus-tx.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    plutus-tx-plugin.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
    # This package's tests require doctest, which generates Haskell source
    # code. However, it does not add derivation strategies in said code,
    # which will fail the build with -Werror. Furthermore, barring an
    # upstream fix, there's nothing we can do about it other than
    # disabling -Werror on it.
    prettyprinter-configurable.ghcOptions = l.mkIf isNotGhc8107 [ "-Werror" ];
  };


  modules = [{ inherit packages; }];

in

{ inherit sha256map modules cabalProjectLocal shellBuildInputs; }

