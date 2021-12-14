############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, rPackages
, haskell-nix
, agdaWithStdlib
, gitignore-nix
, z3
, R
, libsodium-vrf
, checkMaterialization
, compiler-nix-name
, enableHaskellProfiling
  # Whether to set the `defer-plugin-errors` flag on those packages that need
  # it. If set to true, we will also build the haddocks for those packages.
, deferPluginErrors
, topLevelPkgs
, ghcjsPluginPkgs ? null
, cabalProjectLocal ? null
}@args:
let
  compiler-nix-name = if topLevelPkgs.stdenv.hostPlatform.isGhcjs then "ghc8107" else args.compiler-nix-name;
  r-packages = with rPackages; [ R tidyverse dplyr stringr MASS plotly shiny shinyjs purrr ];
  project = haskell-nix.cabalProject' ({ pkgs, ... }: {
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
    # At the moment, we only need one but conceivably we might need one for darwin in future.
    # See https://github.com/input-output-hk/nix-tools/issues/97
    materialized =
      if pkgs.stdenv.hostPlatform.isLinux then (if topLevelPkgs.stdenv.hostPlatform.isGhcjs then ./materialized-ghcjs-build else ./materialized-linux)
      else if pkgs.stdenv.hostPlatform.isGhcjs then ./materialized-ghcjs
      else if pkgs.stdenv.hostPlatform.isDarwin then ./materialized-darwin
      else if pkgs.stdenv.hostPlatform.isWindows then ./materialized-windows
      else builtins.error "Don't have materialized files for this platform";
    # If true, we check that the generated files are correct. Set in the CI so we don't make mistakes.
    inherit checkMaterialization;
    sha256map = {
      "https://github.com/Quid2/flat.git"."ee59880f47ab835dbd73bea0847dab7869fc20d8" = "1lrzknw765pz2j97nvv9ip3l1mcpf2zr4n56hwlz0rk7wq7ls4cm";
      "https://github.com/input-output-hk/cardano-base"."dac2841472c444c6fe867ce39ff00d3f9cdb3623" = "10ajqw8z23ijnw8v6j6bg8q3w01pfvqg2l1khlcgpkbm31m0hnhz";
      "https://github.com/input-output-hk/cardano-crypto.git"."07397f0e50da97eaa0575d93bee7ac4b2b2576ec" = "06sdx5ndn2g722jhpicmg96vsrys89fl81k8290b3lr6b1b0w4m3";
      "https://github.com/input-output-hk/cardano-prelude"."fd773f7a58412131512b9f694ab95653ac430852" = "02jddik1yw0222wd6q0vv10f7y8rdgrlqaiy83ph002f9kjx7mh6";
      "https://github.com/input-output-hk/Win32-network"."3825d3abf75f83f406c1f7161883c438dac7277d" = "19wahfv726fa3mqajpqdqhnl9ica3xmf68i254q45iyjcpj1psqx";
    };
    # Configuration settings needed for cabal configure to work when cross compiling
    # for windows. We can't use `modules` for these as `modules` are only applied
    # after cabal has been configured.
    cabalProjectLocal = lib.optionalString pkgs.stdenv.hostPlatform.isWindows ''
      -- When cross compiling for windows we don't have a `ghc` package, so use
      -- the `plutus-ghc-stub` package instead.
      packages:
        stubs/plutus-ghc-stub
      package plutus-tx-plugin
        flags: +use-ghc-stub

      -- Exlcude test that use `doctest`.  They will not work for windows
      -- cross compilation and `cabal` will not be able to make a plan.
      package prettyprinter-configurable
        tests: False
    '' + lib.optionalString pkgs.stdenv.hostPlatform.isGhcjs ''
      packages:
        stubs/cardano-api-stub
        stubs/iohk-monitoring-stub
        stubs/plutus-ghc-stub
        contrib/*
      package plutus-tx-plugin
        flags: +use-ghc-stub
      package prettyprinter-configurable
        tests: False
      package network
        tests: False
      package clock
        tests: False
        benchmarks: False

      allow-newer:
             stm:base

           -- ghc-boot 8.10.4 is not in hackage, so haskell.nix needs consider 8.8.3
           -- when cross compiling for windows or it will fail to find a solution including
           -- a new Win32 version (ghc-boot depends on Win32 via directory)
           , ghc-boot:base
           , ghc-boot:ghc-boot-th
           , snap-server:attoparsec
           , io-streams-haproxy:attoparsec
           , snap-core:attoparsec
           , websockets:attoparsec
           , jsaddle:base64-bytestring
    '' + lib.optionalString (topLevelPkgs.stdenv.hostPlatform.isGhcjs && !pkgs.stdenv.hostPlatform.isGhcjs) ''
      packages:
        ${topLevelPkgs.buildPackages.haskell-nix.compiler.${compiler-nix-name}.project.configured-src}
        contrib/double-conversion-2.0.2.0
        contrib/lzma-0.0.0.3
        contrib/cardano-crypto-07397f

      allow-newer: ghcjs:base16-bytestring
                 , ghcjs:aeson
                 , stm:base
                 , cardano-binary:recursion-schemes
                 , jsaddle:ghcjs-base
                 , ghcjs-base:primitive
                 , ghcjs-base:time
                 , ghcjs-base:hashable
                 , ghcjs-base:aeson
                 , servant-foreign:lens
                 , servant-client:http-client
      constraints: plutus-tx-plugin +ghcjs-plugin,
                   ghci +ghci

      package ghci
        flags: +ghci

      package plutus-tx-plugin
        flags: +ghcjs-plugin

      -- The following is needed because Nix is doing something crazy.
      package byron-spec-ledger
        tests: False

      package marlowe
        tests: False

      package plutus-doc
        tests: False

      package prettyprinter-configurable
        tests: False

      package small-steps
        tests: False

      package small-steps-test
        tests: False

      package byron-spec-chain
        tests: False
    '';
    modules = [
      ({ pkgs, ... }: lib.mkIf (pkgs.stdenv.hostPlatform != pkgs.stdenv.buildPlatform) {
        packages = {
          # Needs agda
          plutus-metatheory.package.buildable = false;
          # These need R
          plutus-core.components.benchmarks.cost-model-test.buildable = lib.mkForce false;
          plutus-core.components.benchmarks.update-cost-model.buildable = lib.mkForce false;
        };
      })
      ({ pkgs, ... }:
        let
          # Add symlinks to the DLLs used by executable code to the `bin` directory
          # of the components with we are going to run.
          # We should try to find a way to automate this will in haskell.nix.
          symlinkDlls = ''
            ln -s ${libsodium-vrf}/bin/libsodium-23.dll $out/bin/libsodium-23.dll
            ln -s ${pkgs.buildPackages.gcc.cc}/x86_64-w64-mingw32/lib/libgcc_s_seh-1.dll $out/bin/libgcc_s_seh-1.dll
            ln -s ${pkgs.buildPackages.gcc.cc}/x86_64-w64-mingw32/lib/libstdc++-6.dll $out/bin/libstdc++-6.dll
            ln -s ${pkgs.windows.mcfgthreads}/bin/mcfgthread-12.dll $out/bin/mcfgthread-12.dll
          '';
        in
        lib.mkIf (pkgs.stdenv.hostPlatform.isWindows) {
          packages = {
            # Add dll symlinks to the compoents we want to run.
            plutus-core.components.tests.plutus-core-test.postInstall = symlinkDlls;
            plutus-core.components.tests.plutus-ir-test.postInstall = symlinkDlls;
            plutus-core.components.tests.untyped-plutus-core-test.postInstall = symlinkDlls;
            plutus-ledger-api.components.tests.plutus-ledger-api-test.postInstall = symlinkDlls;

            # These three tests try to use `diff` and the following could be used to make the
            # linux version of diff available.  Unfortunately the paths passed to it are windows style.
            # plutus-core.components.tests.plutus-core-test.build-tools = [ pkgs.buildPackages.diffutils ];
            # plutus-core.components.tests.plutus-ir-test.build-tools = [ pkgs.buildPackages.diffutils ];
            # plutus-core.components.tests.untyped-plutus-core-test.build-tools = [ pkgs.buildPackages.diffutils ];
            plutus-core.components.tests.plutus-core-test.buildable = lib.mkForce false;
            plutus-core.components.tests.plutus-ir-test.buildable = lib.mkForce false;
            plutus-core.components.tests.untyped-plutus-core-test.buildable = lib.mkForce false;
          };
        }
      )
      ({ pkgs, config, ... }: {
        packages = {
          ghcjs.components.library.build-tools = let alex = pkgs.haskell-nix.tool compiler-nix-name "alex" {
            index-state = pkgs.haskell-nix.internalHackageIndexState;
            version = "3.2.5";
          }; in [ alex ];
          ghcjs.flags.use-host-template-haskell = true;

          # This is important. We may be reinstalling lib:ghci, and if we do
          # it *must* have the ghci flag enabled (default is disabled).
          ghci.flags.ghci = true;

          plutus-tx-plugin.ghcOptions =
            if (ghcjsPluginPkgs != null && pkgs.stdenv.hostPlatform.isGhcjs)
            then
              (
                let attr = ghcjsPluginPkgs.haskell.projectPackages.plutus-tx-plugin.components.library;
                in
                [
                  "-host-package-db ${attr.passthru.configFiles}/${attr.passthru.configFiles.packageCfgDir}"
                  "-host-package-db ${attr}/package.conf.d"
                  #                                              "-Werror"
                ]
              )
            else __trace "nativePlutus is null" [ ];

          plutus-errors.ghcOptions =
            if (ghcjsPluginPkgs != null && pkgs.stdenv.hostPlatform.isGhcjs)
            then
              (
                let attr = ghcjsPluginPkgs.haskell.projectPackages.plutus-tx-plugin.components.library;
                in
                [
                  "-host-package-db ${attr.passthru.configFiles}/${attr.passthru.configFiles.packageCfgDir}"
                  "-host-package-db ${attr}/package.conf.d"
                  "-Werror"
                ]
              )
            else __trace "nativePlutus is null" [ ];

          plutus-benchmark.ghcOptions =
            if (ghcjsPluginPkgs != null && pkgs.stdenv.hostPlatform.isGhcjs)
            then
              (
                let attr = ghcjsPluginPkgs.haskell.projectPackages.plutus-tx-plugin.components.library;
                in
                [
                  "-host-package-db ${attr.passthru.configFiles}/${attr.passthru.configFiles.packageCfgDir}"
                  "-host-package-db ${attr}/package.conf.d"
                  "-Werror"
                ]
              )
            else __trace "nativePlutus is null" [ ];

          plutus-tx-plugin.components.tests.plutus-tx-tests.ghcOptions =
            if (ghcjsPluginPkgs != null && pkgs.stdenv.hostPlatform.isGhcjs)
            then
              (
                let attr = ghcjsPluginPkgs.haskell.projectPackages.plutus-tx-plugin.components.library;
                in
                [
                  "-host-package-db ${attr.passthru.configFiles}/${attr.passthru.configFiles.packageCfgDir}"
                  "-host-package-db ${attr}/package.conf.d"
                  "-Werror"
                ]
              )
            else __trace "nativePlutus is null" [ ];

          Cabal.patches = [ ../../patches/cabal.patch ];

          # Packages we just don't want docs for
          plutus-benchmark.doHaddock = false;
          # FIXME: Haddock mysteriously gives a spurious missing-home-modules warning
          plutus-tx-plugin.doHaddock = false;

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

          # Werror everything. This is a pain, see https://github.com/input-output-hk/haskell.nix/issues/519
          plutus-core.ghcOptions = [ "-Werror" ];
          # FIXME: has warnings in generated code
          #plutus-metatheory.package.ghcOptions = "-Werror";
          #plutus-benchmark.ghcOptions = [ "-Werror" ];
          #plutus-errors.ghcOptions = [ "-Werror" ];
          plutus-ledger-api.ghcOptions = [ "-Werror" ];
          plutus-tx.ghcOptions = [ "-Werror" ];
          #plutus-tx-plugin.ghcOptions = [ "-Werror" ];
          prettyprinter-configurable.ghcOptions = [ "-Werror" ];
          word-array.ghcOptions = [ "-Werror" ];

          # External package settings

          inline-r.ghcOptions = [ "-XStandaloneKindSignatures" ];

          # Honestly not sure why we need this, it has a mysterious unused dependency on "m"
          # This will go away when we upgrade nixpkgs and things use ieee754 anyway.
          ieee.components.library.libs = lib.mkForce [ ];
        };
      })
      ({ pkgs, ... }: lib.mkIf (!pkgs.stdenv.hostPlatform.isGhcjs) {
        packages = {
          # See https://github.com/input-output-hk/iohk-nix/pull/488
          cardano-crypto-praos.components.library.pkgconfig = lib.mkForce [ [ libsodium-vrf ] ];
          cardano-crypto-class.components.library.pkgconfig = lib.mkForce [ [ libsodium-vrf ] ];
        };
      })
      # For GHCJS
      ({ packages.ghcjs.src = topLevelPkgs.buildPackages.haskell-nix.compiler.${compiler-nix-name}.project.configured-src; })
      (lib.mkIf (topLevelPkgs.stdenv.hostPlatform.isGhcjs) {
        packages.double-conversion.components.library.libs = lib.mkForce [ ];
      })
      ({ pkgs, ... }: lib.mkIf (pkgs.stdenv.hostPlatform.isGhcjs) {
        packages =
          let
            runEmscripten = ''
              patchShebangs jsbits/emscripten/build.sh
              (cd jsbits/emscripten && PATH=${
                  # The extra buildPackages here is for closurecompiler.
                  # Without it we get `unknown emulation for platform: js-unknown-ghcjs` errors.
                  lib.makeBinPath (with pkgs.buildPackages.buildPackages;
                    [ emscripten closurecompiler coreutils python2 ])
                }:$PATH ./build.sh)
            '';
            libsodium-vrf = pkgs.libsodium-vrf.overrideAttrs (attrs: {
              nativeBuildInputs = attrs.nativeBuildInputs or [ ] ++ (with pkgs.buildPackages.buildPackages; [ emscripten python2 ]);
              prePatch = ''
                export HOME=$(mktemp -d)
                export PYTHON=${pkgs.buildPackages.buildPackages.python2}/bin/python
              '' + attrs.prePatch or "";
              configurePhase = ''
                emconfigure ./configure --prefix=$out --enable-minimal --disable-shared --without-pthreads --disable-ssp --disable-asm --disable-pie CFLAGS=-Os
              '';
              CC = "emcc";
            });
          in
          {
            cardano-wallet-core.components.library.build-tools = [ pkgs.buildPackages.buildPackages.gitReallyMinimal ];
            lzma.components.library.libs = lib.mkForce [ pkgs.buildPackages.lzma ];
            cardano-crypto-praos.components.library.pkgconfig = lib.mkForce [ [ libsodium-vrf ] ];
            cardano-crypto-class.components.library.pkgconfig = lib.mkForce [ [ libsodium-vrf ] ];
            cardano-crypto-class.components.library.build-tools = with pkgs.buildPackages.buildPackages; [ emscripten python2 ];
            cardano-crypto-class.components.library.preConfigure = ''
              ls -l
              emcc $(js-unknown-ghcjs-pkg-config --libs --cflags libsodium) jsbits/libsodium.c -o jsbits/libsodium.js -s WASM=0 \
                -s "EXTRA_EXPORTED_RUNTIME_METHODS=['printErr']" \
                -s "EXPORTED_FUNCTIONS=['_malloc', '_free', '_crypto_generichash_blake2b', '_crypto_generichash_blake2b_final', '_crypto_generichash_blake2b_init', '_crypto_generichash_blake2b_update', '_crypto_hash_sha256', '_crypto_hash_sha256_final', '_crypto_hash_sha256_init', '_crypto_hash_sha256_update', '_crypto_sign_ed25519_detached', '_crypto_sign_ed25519_seed_keypair', '_crypto_sign_ed25519_sk_to_pk', '_crypto_sign_ed25519_sk_to_seed', '_crypto_sign_ed25519_verify_detached', '_sodium_compare', '_sodium_free', '_sodium_init', '_sodium_malloc', '_sodium_memzero']"
            '';
            plutus-core.ghcOptions = [ "-Wno-unused-packages" ];
            iohk-monitoring.ghcOptions = [ "-Wno-deprecations" ]; # TODO find alternative fo libyaml
            plutus-pab.components.tests.psgenerator.buildable = false;
            cryptonite.components.library.preConfigure = runEmscripten;
            cardano-crypto.components.library.preConfigure = runEmscripten;
            direct-sqlite.components.library.preConfigure = runEmscripten;
            ghcjs-c-interop.components.library.preConfigure = runEmscripten;
          };
      })
    ] ++ lib.optional enableHaskellProfiling {
      enableLibraryProfiling = true;
      enableExecutableProfiling = true;
    };
  });

in
project
