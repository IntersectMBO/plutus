{ repoRoot, pkgs, ... }:

cabalProject:

{
  name = "plutus";


  packages = [
    repoRoot.nix.agda-with-stdlib

    # R environment
    repoRoot.nix.r-with-packages
    pkgs.R

    # Misc useful stuff, could make these commands but there's a lot already
    pkgs.jekyll
    pkgs.plantuml
    pkgs.jq
    pkgs.yq
    pkgs.gnused
    pkgs.awscli2
    pkgs.act
    pkgs.bzip2
    pkgs.gawk

    # Needed to make building things work, not for commands
    pkgs.zlib
    pkgs.cacert
  ];


  scripts.assemble-changelog = {
    description = "Assembles the changelog for PACKAGE at VERSION";
    exec = repoRoot.scripts.assemble-changelog;
    group = "changelog";
  };


  scripts.prepare-release = {
    description = "Prepares to release PACKAGEs at VERSION";
    exec = repoRoot.scripts.prepare-release;
    group = "changelog";
  };


  scripts.update-version = {
    description = "Updates the version for PACKAGE to VERSION";
    exec = repoRoot.scripts.update-version;
    group = "changelog";
  };


  preCommit = {
    stylish-haskell.enable = true;
    cabal-fmt.enable = true;
    shellcheck.enable = true;
    editorconfig-checker.enable = true;
    nixpkgs-fmt.enable = true;
    optipng.enable = true;
    hlint.enable = false;
  };


  tools.haskellCompiler = cabalProject.args.compiler-nix-name;
}
