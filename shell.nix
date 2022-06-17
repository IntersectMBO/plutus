{ system ? builtins.currentSystem
, enableHaskellProfiling ? false
, packages ? import ./. { inherit system enableHaskellProfiling; }
}:
let
  inherit (packages) pkgs plutus docs;
  inherit (pkgs) stdenv lib utillinux python3 nixpkgs-fmt glibcLocales;
  inherit (plutus) haskell agdaPackages stylish-haskell sphinxcontrib-haddock sphinx-markdown-tables sphinxemoji nix-pre-commit-hooks;
  inherit (plutus) agdaWithStdlib;

  # For Sphinx, and ad-hoc usage
  sphinxTools = python3.withPackages (ps: [
    sphinxcontrib-haddock.sphinxcontrib-domaintools
    sphinx-markdown-tables
    sphinxemoji
    ps.sphinxcontrib_plantuml
    ps.sphinxcontrib-bibtex
    ps.sphinx
    ps.sphinx_rtd_theme
    ps.recommonmark
  ]);

  # Configure project pre-commit hooks
  pre-commit-check = nix-pre-commit-hooks.run {
    src = (lib.cleanSource ./.);
    tools = {
      stylish-haskell = stylish-haskell;
      nixpkgs-fmt = nixpkgs-fmt;
      shellcheck = pkgs.shellcheck;
    };
    hooks = {
      stylish-haskell.enable = true;
      nixpkgs-fmt = {
        enable = true;
        # While nixpkgs-fmt does exclude patterns specified in `.ignore` this
        # does not appear to work inside the hook. For now we have to thus
        # maintain excludes here *and* in `./.ignore` and *keep them in sync*.
        excludes = [ ".*nix/pkgs/haskell/materialized.*/.*" ".*/spago-packages.nix$" ".*/packages.nix$" ];
      };
      shellcheck.enable = true;
      png-optimization = {
        enable = true;
        name = "png-optimization";
        description = "Ensure that PNG files are optimized";
        entry = "${pkgs.optipng}/bin/optipng";
        files = "\\.png$";
      };
    };
  };

  nixFlakesAlias = pkgs.runCommand "nix-flakes-alias" { } ''
    mkdir -p $out/bin
    ln -sv ${pkgs.nixFlakes}/bin/nix $out/bin/nix-flakes
  '';

  # build inputs from nixpkgs ( -> ./nix/default.nix )
  nixpkgsInputs = (with pkgs; [
    # For scripts/s3-sync-unzip.sh
    awscli2
    # For scripts/s3-sync-unzip.sh
    bzip2
    cacert
    editorconfig-core-c
    ghcid
    jq
    # See https://github.com/cachix/pre-commit-hooks.nix/issues/148 for why we need this
    pre-commit
    nixFlakesAlias
    nixpkgs-fmt
    shellcheck
    wget
    yq
    zlib
  ] ++ (lib.optionals (!stdenv.isDarwin) [ rPackages.plotly R ]));

  # local build inputs ( -> ./nix/pkgs/default.nix )
  localInputs = (with plutus; [
    cabal-install
    cardano-repo-tool
    fixPngOptimization
    fixStylishHaskell
    haskell-language-server
    haskell-language-server-wrapper
    hie-bios
    hlint
    stylish-haskell
    docs.build-and-serve-docs
  ]);

in
haskell.project.shellFor {
  nativeBuildInputs = nixpkgsInputs ++ localInputs ++ [ agdaWithStdlib sphinxTools ];
  # We don't currently use this, and it's a pain to materialize, and otherwise
  # costs a fair bit of eval time.
  withHoogle = false;

  shellHook = ''
    ${pre-commit-check.shellHook}
  '';

  # This is no longer set automatically as of more recent `haskell.nix` revisions,
  # but is useful for users with LANG settings.
  LOCALE_ARCHIVE = lib.optionalString (stdenv.hostPlatform.libc == "glibc") "${glibcLocales}/lib/locale/locale-archive";
}
