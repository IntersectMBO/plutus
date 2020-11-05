{ pkgs
, pkgsMusl
, checkMaterialization
, system ? builtins.currentSystem
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }
, rev ? null
, sources
}:

let

  iohkNix =
    let
      sources = import ../sources.nix;
    in
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
    inherit pkgsMusl;
    inherit (pkgs) stdenv fetchFromGitHub fetchFromGitLab haskell-nix buildPackages nix-gitignore z3 R rPackages;
    inherit agdaPackages checkMaterialization;
  };


  #
  # additional haskell packages from ./nix/pkgs/haskell-extra
  #
  exeFromExtras = x: haskell.extraPackages."${x}".components.exes."${x}";
  purty = exeFromExtras "purty";
  cabal-install = haskell.extraPackages.cabal-install.components.exes.cabal;
  stylish-haskell = exeFromExtras "stylish-haskell";
  hlint = exeFromExtras "hlint";
  haskell-language-server = exeFromExtras "haskell-language-server";
  hie-bios = exeFromExtras "hie-bios";
  haskellNixAgda = haskell.extraPackages.Agda;

  # The Agda builder needs a derivation with:
  # - The 'agda' executable
  # - The 'agda-mode' executable
  # - A 'version' attribute
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
    pkgs.callPackage ./../lib/agda { Agda = frankenAgda; };

  #
  # dev convenience scripts
  #
  fixPurty = pkgs.callPackage ./fix-purty { inherit purty; };
  fixStylishHaskell = pkgs.callPackage ./fix-stylish-haskell { inherit stylish-haskell; };
  updateMaterialized = haskell.project.stack-nix.passthru.updateMaterialized;
  updateMetadataSamples = pkgs.callPackage ./update-metadata-samples { };
  updateClientDeps = pkgs.callPackage ./update-client-deps {
    inherit purty;
    inherit (pkgs.nodePackages_10_x) node-gyp;
    inherit (pkgs.yarn2nix-moretea) yarn2nix;
    inherit (easyPS) purs psc-package spago spago2nix;
    inherit (pkgs.stdenv) isDarwin;
    inherit (pkgs) clang;
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


  # not available in 20.03 and we depend on several recent changes
  # including stylish-haskell support
  nix-pre-commit-hooks = import (sources."pre-commit-hooks.nix");

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

  # sphinx haddock support
  sphinxcontrib-haddock = pkgs.callPackage (sources.sphinxcontrib-haddock) { pythonPackages = pkgs.python3Packages; };

  # nodejs headers  (needed for purescript builds)
  nodejs-headers = sources.nodejs-headers;

in
{
  inherit sphinx-markdown-tables sphinxemoji sphinxcontrib-haddock;
  inherit nix-pre-commit-hooks nodejs-headers;
  inherit haskell agdaPackages cabal-install stylish-haskell hlint haskell-language-server hie-bios purty;
  inherit fixPurty fixStylishHaskell updateMaterialized updateMetadataSamples updateClientDeps;
  inherit iohkNix set-git-rev;
  inherit easyPS;
}
