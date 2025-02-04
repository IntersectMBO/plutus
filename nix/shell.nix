{ inputs, pkgs, lib, project, agda-with-stdlib, r-with-packages }:

let
  cabal-tool = project.tool "cabal" "latest";
  cabal = cabal-tool.project.hsPkgs.cabal-install.components.exes.cabal;

  cabal-fmt-project = pkgs.haskell-nix.hackage-project {
    name = "cabal-fmt";
    compiler-nix-name = "ghc966";
  };
  cabal-fmt = cabal-fmt-project.hsPkgs.cabal-fmt.components.exes.cabal-fmt;

  hls-tool = project.tool "haskell-language-server"
    {
      ghc8107 = "2.2.0.0";
      ghc966 = "latest";
      ghc984 = "latest";
      ghc9101 = "latest";
    }.${project.args.compiler-nix-name};

  getHlsTool = name:
    if hls-tool.project.hsPkgs ? name then
      hls-tool.project.hsPkgs.${name}.components.exes.${name}
    else
      null;

  haskell-language-server = getHlsTool "haskell-language-server";
  stylish-haskell = getHlsTool "stylish-haskell";
  fourmolu = getHlsTool "fourmolu";
  hlint = getHlsTool "hlint";

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
    inputs.nixpkgs-2405.legacyPackages.${pkgs.system}.linkchecker
    haskell-language-server
    stylish-haskell
    fourmolu
    cabal
    hlint
    cabal-fmt

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
  ];

in

project.shellFor {

  name = "plutus-shell-${project.args.compiler-nix-name}";

  buildInputs = lib.concatLists [
    common-pkgs
    linux-pkgs
    pre-commit-check.enabledPackages
  ];

  withHoogle = true;

  shellHook = ''
    eval "$(starship init bash)"
    ${pre-commit-check.shellHook}
    echo -e "\n🤟 Welcome to Plutus 🤟"
  '';
}
