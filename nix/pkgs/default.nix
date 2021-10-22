{ pkgs
, checkMaterialization
, system ? builtins.currentSystem
, config ? { }
, sources
, enableHaskellProfiling
}:
let
  inherit (pkgs) stdenv;

  gitignore-nix = pkgs.callPackage sources.gitignore-nix { };

  # { index-state, compiler-nix-name, project, projectPackages, packages, extraPackages }
  haskell = pkgs.callPackage ./haskell {
    inherit gitignore-nix sources;
    inherit agdaWithStdlib checkMaterialization enableHaskellProfiling;

    # This ensures that the utility scripts produced in here will run on the current system, not
    # the build system, so we can run e.g. the darwin ones on linux
    inherit (pkgs.evalPackages) writeShellScript;
  };

  #
  # additional haskell packages from ./nix/pkgs/haskell-extra
  #
  exeFromExtras = x: haskell.extraPackages."${x}".components.exes."${x}";
  cabal-install = haskell.extraPackages.cabal-install.components.exes.cabal;
  cardano-repo-tool = exeFromExtras "cardano-repo-tool";
  stylish-haskell = exeFromExtras "stylish-haskell";
  hlint = exeFromExtras "hlint";
  haskell-language-server = exeFromExtras "haskell-language-server";
  haskell-language-server-wrapper = pkgs.writeShellScriptBin "haskell-language-server-wrapper" ''${haskell-language-server}/bin/haskell-language-server "$@"'';
  hie-bios = exeFromExtras "hie-bios";
  haskellNixAgda = haskell.extraPackages.Agda;

  # We want to keep control of which version of Agda we use, so we supply our own and override
  # the one from nixpkgs.
  #
  # The Agda builder needs a derivation with:
  # - The 'agda' executable
  # - The 'agda-mode' executable
  # - A 'version' attribute
  #
  # So we stitch one together here.
  #
  # Furthermore, the agda builder uses a `ghcWithPackages` that has to have ieee754 available.
  # We'd like it to use the same GHC as we have, if nothing else just to avoid depending on
  # another GHC from nixpkgs! Sadly, this one is harder to override, and we just hack
  # it into pkgs.haskellPackages in a fragile way. Annoyingly, this also means we have to ensure
  # we have a few extra packages that it uses in our Haskell package set.
  agdaPackages =
    let
      frankenAgda = (pkgs.symlinkJoin {
        name = "agda";
        paths = [
          haskellNixAgda.components.exes.agda
          haskellNixAgda.components.exes.agda-mode
        ];
      }) // { version = haskellNixAgda.identifier.version; };
      frankenPkgs = pkgs // { haskellPackages = pkgs.haskellPackages // { ghcWithPackages = haskell.project.ghcWithPackages; }; };
    in
    pkgs.agdaPackages.override { Agda = frankenAgda; pkgs = frankenPkgs; };

  agdaWithStdlib =
    # Need a newer version for 2.6.2 compatibility
    let stdlib = agdaPackages.standard-library.overrideAttrs (oldAtts: rec {
      version = "1.7";
      src = pkgs.fetchFromGitHub {
        repo = "agda-stdlib";
        owner = "agda";
        rev = "v${version}";
        sha256 = "14h3jprm6924g9576v25axn9v6xnip354hvpzlcqsc5qqyj7zzjs";
      };
      # This is preConfigure is copied from more recent nixpkgs that also uses version 1.7 of standard-library
      # Old nixpkgs (that used 1.4) had a preConfigure step that worked with 1.7
      # Less old nixpkgs (that used 1.6) had a preConfigure step that attempts to `rm` files that are now in the
      # .gitignore list for 1.7
      preConfigure = ''
        runhaskell GenerateEverything.hs
        # We will only build/consider Everything.agda, in particular we don't want Everything*.agda
        # do be copied to the store.
        rm EverythingSafe.agda
      '';
    });

    in agdaPackages.agda.withPackages [ stdlib ];

  #
  # dev convenience scripts
  #
  fixStylishHaskell = pkgs.callPackage ./fix-stylish-haskell { inherit stylish-haskell; };
  fixPngOptimization = pkgs.callPackage ./fix-png-optimization { };
  updateMaterialized = pkgs.writeShellScriptBin "updateMaterialized" ''
    # This runs the 'updateMaterialize' script in all platform combinations we care about.
    # See the comment in ./haskell/haskell.nix

    # Update the linux files (will do for all unixes atm).
    $(nix-build default.nix -A plutus.haskell.project.plan-nix.passthru.updateMaterialized --argstr system x86_64-linux)
    $(nix-build default.nix -A plutus.haskell.project.plan-nix.passthru.updateMaterialized --argstr system x86_64-darwin)
    $(nix-build default.nix -A plutus.haskell.project.plan-nix.passthru.updateMaterialized --argstr system windows)
    $(nix-build default.nix -A plutus.haskell.project.projectCross.mingwW64.plan-nix.passthru.updateMaterialized --argstr system x86_64-linux)

    # This updates the sha files for the extra packages
    $(nix-build default.nix -A plutus.haskell.extraPackages.updateAllShaFiles --argstr system x86_64-linux)
    $(nix-build default.nix -A plutus.haskell.extraPackages.updateAllShaFiles --argstr system x86_64-darwin)
  '';

  #
  # sphinx python packages
  #
  sphinx-markdown-tables = pkgs.python3Packages.callPackage ./sphinx-markdown-tables { };
  sphinxemoji = pkgs.python3Packages.callPackage ./sphinxemoji { };

  # By default pre-commit-hooks.nix uses its own pinned version of nixpkgs. In order to
  # to get it to use our version we have to (somewhat awkwardly) use `nix/default.nix`
  # to which both `nixpkgs` and `system` can be passed.
  nix-pre-commit-hooks = (pkgs.callPackage (sources.pre-commit-hooks-nix + "/nix/default.nix") {
    inherit system;
    inherit (sources) nixpkgs;
  });

  # sphinx haddock support
  sphinxcontrib-haddock = pkgs.callPackage (sources.sphinxcontrib-haddock) { pythonPackages = pkgs.python3Packages; };

  # combined haddock documentation for all public plutus libraries
  plutus-haddock-combined =
    let
      haddock-combine = pkgs.callPackage ../lib/haddock-combine.nix {
        ghc = haskell.projectAllHaddock.pkg-set.config.ghc.package;
        inherit (sphinxcontrib-haddock) sphinxcontrib-haddock;
      };
    in
    pkgs.callPackage ./plutus-haddock-combined {
      inherit haskell haddock-combine;
      inherit (pkgs) haskell-nix;
    };

  # Collect everything to be exported under `plutus.lib`: builders/functions/utils
  lib = rec {
    inherit gitignore-nix;
    haddock-combine = pkgs.callPackage ../lib/haddock-combine.nix { inherit sphinxcontrib-haddock; };
    latex = pkgs.callPackage ../lib/latex.nix { };
  };

in
{
  inherit sphinx-markdown-tables sphinxemoji sphinxcontrib-haddock;
  inherit nix-pre-commit-hooks;
  inherit haskell agdaPackages cabal-install cardano-repo-tool stylish-haskell hlint haskell-language-server haskell-language-server-wrapper hie-bios;
  inherit fixStylishHaskell fixPngOptimization updateMaterialized;
  inherit plutus-haddock-combined;
  inherit agdaWithStdlib;
  inherit lib;
}
