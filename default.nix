########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################

{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { allowUnfreePredicate = (import ./nix/lib/unfree.nix).unfreePredicate; }
  # Overrides for niv
, sourcesOverride ? { }
, packages ? import ./nix { inherit system crossSystem config sourcesOverride rev checkMaterialization enableHaskellProfiling; }
  # An explicit git rev to use, passed when we are in Hydra
, rev ? null
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
  # Whether to build our Haskell packages (and their dependencies) with profiling enabled.
, enableHaskellProfiling ? false
}:
let
  inherit (packages) pkgs plutus sources;
  inherit (pkgs) lib haskell-nix;
  inherit (plutus) haskell iohkNix git-rev set-git-rev agdaPackages;
  inherit (plutus) easyPS sphinxcontrib-haddock;
in
rec {
  inherit pkgs plutus;

  inherit (plutus) web-ghc;

  inherit (haskell.packages.plutus-pab.components.exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet;

  inherit (haskell.packages.marlowe.components.exes) marlowe-app;

  webCommon = pkgs.callPackage ./web-common { inherit (plutus.lib) gitignore-nix; };
  webCommonPlutus = pkgs.callPackage ./web-common-plutus { inherit (plutus.lib) gitignore-nix; };
  webCommonMarlowe = pkgs.callPackage ./web-common-marlowe { inherit (plutus.lib) gitignore-nix; };
  webCommonPlayground = pkgs.callPackage ./web-common-playground { inherit (plutus.lib) gitignore-nix; };

  plutus-playground = pkgs.recurseIntoAttrs rec {
    tutorial = docs.site;
    haddock = plutus.plutus-haddock-combined;

    inherit (pkgs.callPackage ./plutus-playground-client {
      inherit (plutus.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit set-git-rev haskell webCommon webCommonPlutus webCommonPlayground;
    }) client server-invoker generated-purescript generate-purescript start-backend;
  };

  marlowe-playground = pkgs.recurseIntoAttrs rec {
    tutorial = docs.marlowe-tutorial;

    inherit (pkgs.callPackage ./marlowe-playground-client {
      inherit (plutus.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit set-git-rev haskell webCommon webCommonMarlowe webCommonPlayground;
    }) client server-invoker generated-purescript generate-purescript start-backend;
  };

  marlowe-dashboard = pkgs.recurseIntoAttrs rec {
    inherit (pkgs.callPackage ./marlowe-dashboard-client {
      inherit plutus-pab;
      inherit (plutus.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit webCommon webCommonMarlowe;
    }) client server-invoker generated-purescript generate-purescript;
  };

  marlowe-marketplace = pkgs.recurseIntoAttrs rec {
    inherit (pkgs.callPackage ./marlowe-marketplace-client {
      inherit (plutus.lib) buildPursPackage buildNodeModules filterNpm gitignore-nix;
      inherit webCommon webCommonMarlowe;
    }) client;
  };

  plutus-pab = pkgs.recurseIntoAttrs (pkgs.callPackage ./plutus-pab-client {
    inherit (plutus.lib) buildPursPackage buildNodeModules gitignore-nix filterNpm;
    inherit set-git-rev haskell webCommon webCommonPlutus;
  });

  tests = import ./nix/tests/default.nix {
    inherit pkgs iohkNix;
    inherit (plutus) fixStylishHaskell fixPurty;
    inherit (pkgs) terraform;
    src = ./.;
  };

  docs = import ./nix/docs.nix { inherit pkgs plutus; };

  deployment = pkgs.callPackage ./deployment {
    inherit plutus marlowe-playground plutus-playground;
  };

  # This builds a vscode devcontainer that can be used with the plutus-starter project (or probably the plutus project itself).
  devcontainer =
    let
      shell = (haskell.project.shellFor { withHoogle = false; });
      # This is an evil hack to allow us to have a docker container with a "similar" environment to
      # our haskell.nix shell without having it actually run nix-shell. In particular, we need some
      # of the flags that the stdenv setup hooks set based on the build inputs, like NIX_LDFLAGS.
      # The result of this derivation is a file that can be sourced to set the variables we need.
      horrible-env-vars-hack = pkgs.runCommand "exfiltrate-env-vars"
        {
          inherit (shell) buildInputs nativeBuildInputs propagatedBuildInputs;
        } ''
        set | grep -v -E '^BASHOPTS=|^BASH_VERSINFO=|^EUID=|^PPID=|^SHELLOPTS=|^UID=|^HOME=|^TEMP=|^TMP=|^TEMPDIR=|^TMPDIR=|^NIX_ENFORCE_PURITY=' >> $out
      '';
    in
    pkgs.callPackage (import ./nix/devcontainer) {
      name = "plutus-devcontainer";
      tag = "latest";
      extraContents = [
        shell.ghc
        plutus.haskell-language-server
        plutus.cabal-install
        pkgs.binutils
      ];
      extraCommands = ''
        # Put the environment stuff somewhere convenient
        chmod +w etc
        mkdir -p etc/profile.d
        echo 'set -o allexport' >> etc/profile.d/env.sh
        echo 'source ${horrible-env-vars-hack}' >> etc/profile.d/env.sh
        echo 'set +o allexport' >> etc/profile.d/env.sh

        # We just clobbered this, put it back
        echo 'export PATH=$PATH:/usr/bin:/bin' >> etc/profile.d/env.sh
        echo 'export NIX_BUILD_TOP=$(mktemp -d)' >> etc/profile.d/env.sh

        # Load all the stuff in an interactive session too
        chmod +w root
        echo 'source /etc/profile.d/env.sh' >> root/.bashrc
      '';
    };
}
