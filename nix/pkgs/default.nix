{ pkgs
, plutusMusl
, checkMaterialization
, system ? builtins.currentSystem
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }
, rev ? null
, sources
}:
let
  inherit (pkgs) stdenv;

  iohkNix =
    import sources.iohk-nix {
      inherit system config;
      # Make iohk-nix use our nixpkgs
      sourcesOverride = { inherit (sources) nixpkgs; };
    };

  # The git revision comes from `rev` if available (Hydra), otherwise
  # it is read using IFD and git, which is avilable on local builds.
  git-rev = if isNull rev then iohkNix.commitIdFromGitRepo ../../.git else rev;

  # { index-state, project, projectPackages, packages, muslProject, muslPackages, extraPackages }
  haskell = pkgs.callPackage ./haskell {
    inherit plutusMusl;
    inherit agdaWithStdlib checkMaterialization;
  };

  #
  # additional haskell packages from ./nix/pkgs/haskell-extra
  #
  exeFromExtras = x: haskell.extraPackages."${x}".components.exes."${x}";
  cabal-install = haskell.extraPackages.cabal-install.components.exes.cabal;
  stylish-haskell = exeFromExtras "stylish-haskell";
  hlint = exeFromExtras "hlint";
  haskell-language-server = exeFromExtras "haskell-language-server";
  hie-bios = exeFromExtras "hie-bios";
  gen-hie = haskell.extraPackages.implicit-hie.components.exes.gen-hie;
  haskellNixAgda = haskell.extraPackages.Agda;

  # We want to keep control of which version of Agda we use, so we supply our own and override
  # the one from nixpkgs.
  #
  # The Agda builder needs a derivation with:
  # - The 'agda' executable
  # - The 'agda-mode' executable
  # - A 'version' attribute
  #
  # So we stitch one together here. It doesn't *seem* to need the library interface files,
  # but it seems like they should be there so I added them too.
  agdaPackages =
    let
      frankenAgda = (pkgs.symlinkJoin {
        name = "agda";
        paths = [
          haskellNixAgda.components.exes.agda
          haskellNixAgda.components.exes.agda-mode
          haskellNixAgda.components.library
        ];
      }) // { version = haskellNixAgda.identifier.version; };
    in
    pkgs.agdaPackages.override { Agda = frankenAgda; };

  agdaWithStdlib = agdaPackages.agda.withPackages [ agdaPackages.standard-library ];

  #
  # dev convenience scripts
  #
  fixPurty = pkgs.callPackage ./fix-purty { inherit purty; };
  fixStylishHaskell = pkgs.callPackage ./fix-stylish-haskell { inherit stylish-haskell; };
  updateMaterialized = haskell.project.stack-nix.passthru.updateMaterialized;
  updateHie = pkgs.callPackage ./update-hie { inherit gen-hie; };
  updateMetadataSamples = pkgs.callPackage ./update-metadata-samples { };
  updateClientDeps = pkgs.callPackage ./update-client-deps {
    inherit (easyPS) purs psc-package spago spago2nix;
  };

  #
  # sphinx python packages
  #
  sphinx-markdown-tables = pkgs.python3Packages.callPackage ./sphinx-markdown-tables { };
  sphinxemoji = pkgs.python3Packages.callPackage ./sphinxemoji { };

  # `set-git-rev` is a function that can be called on a haskellPackages
  # package to inject the git revision post-compile
  set-git-rev = pkgs.callPackage ./set-git-rev {
    inherit (haskell.packages) ghcWithPackages;
    inherit git-rev;
  };

  # Thorp is an S3 sync tool used for deployments
  thorp =
    let mvn2nix = import sources.mvn2nix { };
    in
    pkgs.callPackage ./thorp {
      thorpSrc = sources.thorp;
      inherit mvn2nix;
    };

  # not available in 20.03 and we depend on several recent changes
  # including stylish-haskell support
  nix-pre-commit-hooks = import (sources."pre-commit-hooks.nix");

  # purty is unable to process several files but that is what pre-commit
  # does. pre-commit-hooks.nix does provide a wrapper for that but when
  # we pin our own `tools` attribute that gets overwritten so we have to
  # instead provide the wrapper.
  purty-pre-commit = pkgs.callPackage ./purty-pre-commit { inherit purty; };

  # easy-purescript-nix has some kind of wacky internal IFD
  # usage that breaks the logic that makes source fetchers
  # use native dependencies. This isn't easy to fix, since
  # the only places that need to use native dependencies
  # are deep inside, and we don't want to build the whole
  # thing native. Fortunately, we only want to build the
  # client on Linux, so that's okay. However, it does
  # mean that e.g. we can't build the client dep updating
  # script on Darwin.
  easyPS = pkgs.callPackage (sources.easy-purescript-nix) { };
  # We pull out some packages from easyPS that are a pain to get otherwise.
  # In particular, we used to build purty ourselves, but now its build is a nightmare.
  # This does mean we can't as easily control the version we get, though.
  inherit (easyPS) purty purs spago;

  # sphinx haddock support
  sphinxcontrib-haddock = pkgs.callPackage (sources.sphinxcontrib-haddock) { pythonPackages = pkgs.python3Packages; };

  # ghc web service
  web-ghc = pkgs.callPackage ./web-ghc { inherit set-git-rev haskell; };

  # combined haddock documentation for all public plutus libraries
  plutus-haddock-combined =
    let
      haddock-combine = pkgs.callPackage ../lib/haddock-combine.nix {
        ghc = haskell.project.pkg-set.config.ghc.package;
        inherit (sphinxcontrib-haddock) sphinxcontrib-haddock;
      };
    in
    pkgs.callPackage ./plutus-haddock-combined {
      inherit haskell haddock-combine;
      inherit (pkgs) haskell-nix;
    };

  # Collect everything to be exported under `plutus.lib`: builders/functions/utils
  lib = rec {
    haddock-combine = pkgs.callPackage ../lib/haddock-combine.nix { inherit sphinxcontrib-haddock; };
    latex = pkgs.callPackage ../lib/latex.nix { };
    npmlock2nix = (import sources.npmlock2nix { });
    buildPursPackage = pkgs.callPackage ../lib/purescript.nix { inherit easyPS;inherit (pkgs) nodejs; };
    buildNodeModules = pkgs.callPackage ../lib/node_modules.nix ({
      inherit npmlock2nix;
    } // pkgs.lib.optionalAttrs (stdenv.isDarwin) {
      CoreServices = pkgs.darwin.apple_sdk.frameworks.CoreServices;
      xcodebuild = pkgs.xcodebuild;
    });

  };

in
{
  inherit sphinx-markdown-tables sphinxemoji sphinxcontrib-haddock;
  inherit nix-pre-commit-hooks;
  inherit haskell agdaPackages cabal-install stylish-haskell hlint haskell-language-server hie-bios gen-hie;
  inherit purty purty-pre-commit purs spago;
  inherit fixPurty fixStylishHaskell updateMaterialized updateHie updateMetadataSamples updateClientDeps;
  inherit iohkNix set-git-rev web-ghc thorp;
  inherit easyPS plutus-haddock-combined;
  inherit agdaWithStdlib;
  inherit lib;
}
