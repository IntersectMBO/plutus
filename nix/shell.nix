{ inputs, pkgs, lib, project, agda-with-stdlib, r-with-packages }:

let
  haskell-tools = project.tools
    {
      cabal = "latest";
      hlint = "latest";
      haskell-language-server = "latest";
    } // {
    cabal-fmt = pkgs.haskell-nix.hackage-project {
      name = "cabal-fmt";
      compiler-nix-name = "ghc966";
    };
  };

  stylish-haskell = haskell-tools.haskell-language-server.project.hsPkgs.stylish-haskell.components.exes.stylish-haskell;
  fourmolu = haskell-tools.haskell-language-server.project.hsPkgs.fourmolu.components.exes.fourmolu;
  cabal = haskell-tools.cabal.project.hsPkgs.cabal-install.components.exes.cabal;
  hlint = haskell-tools.hlint.project.hsPkgs.hlint.components.exes.hlint;
  cabal-fmt = haskell-tools.cabal-fmt.project.hsPkgs.cabal-fmt.components.exes.cabal-fmt;

  # pkgs.optipng 
  # pkgs.nixfmt-classic 
  # pkgs.shellcheck
  # pkgs.editorconfig-checker

  pre-commit-check = inputs.pre-commit-hooks.lib.${pkgs.system}.run {
    src = ../.;
    hooks = {
      nixpkgs-fmt = {
        enable = true;
        package = pkgs.nixpkgs-fmt;
      };
      # cabal-fmt = {
      #   options = "--inplace";
      #   include = [ "cabal" ];
      # };

      # stylish-haskell = {
      #   options = "--inplace --config .stylish-haskell.yaml";
      #   include = [ "hs" "lhs" ];
      # };

      # fourmolu = {
      #   options = "--mode inplace";
      #   include = [ "hs" "lhs" ];
      # };

      # hlint = {
      #   options = "--hint=.hlint.yaml";
      #   include = [ "hs" "lhs" ];
      # };

      # shellcheck = { 
      #   include = [ "sh" ]; 
      #   package = pkgs.shellcheck;
      # };

      # prettier = { include = [ "ts" "js" "css" "html" ]; };

      # editorconfig-checker = { options = "-config .editorconfig"; };

      # nixfmt-classic = { include = [ "nix" ]; };

      # optipng = { include = [ "png" ]; };

      # purs-tidy = {
      #   options = "format-in-place";
      #   include = [ "purs" ];
      # };

      # rustfmt = { include = [ "rs" ]; };
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
