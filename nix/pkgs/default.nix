{ pkgs
, pkgsMusl
, checkMaterialization
, system ? builtins.currentSystem
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }
, rev ? null
, sources
, enableHaskellProfiling
}:
let
  inherit (pkgs) stdenv;

  iohkNix =
    import sources.iohk-nix {
      inherit system config;
      # Make iohk-nix use our nixpkgs
      sourcesOverride = { inherit (sources) nixpkgs; };
    };

  gitignore-nix = pkgs.callPackage sources."gitignore.nix" { };

  # The git revision comes from `rev` if available (Hydra), otherwise
  # it is read using IFD and git, which is avilable on local builds.
  git-rev = if isNull rev then iohkNix.commitIdFromGitRepo ../../.git else rev;

  # { index-state, project, projectPackages, packages, muslProject, muslPackages, extraPackages }
  haskell = pkgs.callPackage ./haskell {
    inherit pkgsMusl;
    inherit gitignore-nix;
    inherit agdaWithStdlib checkMaterialization enableHaskellProfiling;
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
  updateMaterialized = pkgs.writeShellScriptBin "updateMaterialized" ''
    # This runs the 'updateMaterialize' script in all platform combinations we care about.
    # See the comment in ./haskell/haskell.nix

    # Update the linux files (will do for all unixes atm).
    $(nix-build default.nix -A plutus.haskell.project.plan-nix.passthru.updateMaterialized --argstr system x86_64-linux)

    # Update the musl files. This isn't quite as simple as just passing a system, since it's inherently a "cross" build,
    # but we actually have a variant project exposed already, so we can just use that.
    $(nix-build default.nix -A plutus.haskell.muslProject.plan-nix.passthru.updateMaterialized --argstr system x86_64-linux)
  '';
  updateHie = pkgs.callPackage ./update-hie { inherit gen-hie; };
  updateMetadataSamples = pkgs.callPackage ./update-metadata-samples { };
  updateClientDeps = pkgs.callPackage ./update-client-deps {
    inherit purs psc-package spago spago2nix;
  };

  #
  # sphinx python packages
  #
  sphinx-markdown-tables = pkgs.python3Packages.callPackage ./sphinx-markdown-tables { };
  sphinxemoji = pkgs.python3Packages.callPackage ./sphinxemoji { };

  # `set-git-rev` is a function that can be called on a haskellPackages
  # package to inject the git revision post-compile
  set-git-rev = pkgs.callPackage ./set-git-rev {
    inherit (haskell.project) ghcWithPackages;
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

  # By default pre-commit-hooks.nix uses its own pinned version of nixpkgs. In order to
  # to get it to use our version we have to (somewhat awkwardly) use `nix/default.nix`
  # to which both `nixpkgs` and `system` can be passed.
  nix-pre-commit-hooks = (pkgs.callPackage ((sources."pre-commit-hooks.nix") + "/nix/default.nix") {
    inherit system;
    inherit (sources) nixpkgs;
  }).packages;

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
  inherit (easyPS) purty purs psc-package spago;

  # There is a spago2nix in easyPS, but it doesn't (currently) work. It doesn't
  # matter because it's actually just a thin call to spago2nix's nix build
  # script. So we can just go directly to the source and get the latest
  # version.
  #
  # It's worth periodically checking to see if the easyPS version is working
  # again. To check:
  #
  # * Replace this call with `inherit (easyPS) spago2nix;`.
  # * Run `nix-shell --run 'cd plutus-playground-client ; update-client-deps'
  #
  # If that fails, it's not ready. Rollback.
  # If it succeeds:
  #
  # * Merge your new `inherit (easyPS) spago2nix` with the one above.
  # * Run `niv delete spago2nix`.
  #
  spago2nix = pkgs.callPackage (sources.spago2nix) { };

  # sphinx haddock support
  sphinxcontrib-haddock = pkgs.callPackage (sources.sphinxcontrib-haddock) { pythonPackages = pkgs.python3Packages; };

  # ghc web service
  web-ghc = pkgs.callPackage ./web-ghc { inherit set-git-rev haskell; };

  # Nixops version after 1.7 release that is on nixpkgs 20.09
  # latest nixops uses nix flakes but unfortunately the below command won't work in restricted mode
  # for now I have commented it out and you can still build `nix-build -A plutus.nixops` however it
  # won't work in nix-shell. To get it to build on Hydra I think we will have to manually provide
  # flake-compat with niv.
  # nixops = (import sources.nixops).defaultPackage."${system}";

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
    inherit gitignore-nix;
    haddock-combine = pkgs.callPackage ../lib/haddock-combine.nix { inherit sphinxcontrib-haddock; };
    latex = pkgs.callPackage ../lib/latex.nix { };
    filterNpm = pkgs.callPackage ../lib/filter-npm.nix { };
    npmlock2nix = pkgs.callPackage sources.npmlock2nix { };
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
  inherit purty purty-pre-commit purs spago spago2nix;
  inherit fixPurty fixStylishHaskell updateMaterialized updateHie updateMetadataSamples updateClientDeps;
  inherit iohkNix set-git-rev web-ghc thorp;
  inherit easyPS plutus-haddock-combined;
  inherit agdaWithStdlib;
  inherit lib;
}
