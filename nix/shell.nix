{ inputs, pkgs, lib, project, agda-with-stdlib, r-with-packages }:

let
  haskell-tools = project.tools
    {
      cabal = "latest";
      hlint = "latest";
      haskell-language-server = "latest";
    }
  //
  {
    cabal-fmt = pkgs.haskell-nix.hackage-project {
      name = "cabal-fmt";
      compiler-nix-name = "ghc966";
    };
  };

  haskell-language-server = haskell-tools.haskell-language-server.project.hsPkgs.haskell-language-server.components.exes.haskell-language-server; # editorconfig-checker-disable-line
  stylish-haskell = haskell-tools.haskell-language-server.project.hsPkgs.stylish-haskell.components.exes.stylish-haskell; # editorconfig-checker-disable-line
  fourmolu = haskell-tools.haskell-language-server.project.hsPkgs.fourmolu.components.exes.fourmolu;
  cabal = haskell-tools.cabal.project.hsPkgs.cabal-install.components.exes.cabal;
  hlint = haskell-tools.hlint.project.hsPkgs.hlint.components.exes.hlint;
  cabal-fmt = haskell-tools.cabal-fmt.hsPkgs.cabal-fmt.components.exes.cabal-fmt;

  pre-commit-check = inputs.pre-commit-hooks.lib.${pkgs.system}.run {
    src = ../.;
    hooks = {
      nixpkgs-fmt = {
        enable = true;
        package = pkgs.nixpkgs-fmt;
      };
      cabal-fmt = {
        enable = true;
        package = cabal-fmt;
      };
      stylish-haskell = {
        enable = true;
        package = stylish-haskell;
        args = [ "--config" ".stylish-haskell.yaml" ];
      };
      fourmolu = {
        enable = false;
        package = fourmolu;
        args = [ "--mode" "inplace" ];
      };
      hlint = {
        enable = false;
        package = hlint;
        args = [ "--hint" ".hlint.yaml" ];
      };
      shellcheck = {
        enable = false;
        package = pkgs.shellcheck;
        args = [ "--hint" ".hlint.yaml" ];
      };
      prettier = {
        enable = false;
        package = pkgs.prettier;
      };
      editorconfig-checker = {
        enable = true;
        args = [ "-config" ".editorconfig" ];
        package = pkgs.editorconfig-checker;
      };
    };
  };

  linux-pkgs = lib.optionals pkgs.hostPlatform.isLinux [
    pkgs.papi
  ];

  common-pkgs = [
    agda-with-stdlib
    r-with-packages

    pkgs.texliveFull
    pkgs.jekyll
    pkgs.plantuml
    pkgs.jq
    pkgs.yq
    pkgs.gnused
    pkgs.awscli2
    pkgs.act
    pkgs.bzip2
    pkgs.gawk
    pkgs.scriv
    pkgs.fswatch
    pkgs.yarn
    pkgs.zlib
    pkgs.cacert
    pkgs.upx
    pkgs.curl
    pkgs.starship
    pkgs.bash
    pkgs.git
    pkgs.which
    pkgs.nodejs_20
    # pkgs.linkchecker
  ];

in

project.shellFor {

  buildInputs = lib.concatLists [
    common-pkgs
    linux-pkgs
    pre-commit-check.enabledPackages
  ];

  withHoogle = true;

  shellHook = ''
    eval "$(starship init bash)"
    ${pre-commit-check.shellHook}
    # {builtins.readFile certEnv}
  '';
}
