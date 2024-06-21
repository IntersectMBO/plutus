{ repoRoot, inputs, pkgs, system, lib }:

cabalProject:

let

  # We need some environment variables from the various ocaml and coq pacakges
  # that the certifier code needs.
  # Devshell doesn't run setup hooks from other packages, so just extract
  # the correct values of the environment variables from the haskell.nix
  # shell and use those.
  certEnv = pkgs.runCommand "cert-env"
    {
      nativeBuildInputs = cabalProject.shell.nativeBuildInputs;
      buildInputs = cabalProject.shell.buildInputs;
    }
    ''
      echo "export COQPATH=$COQPATH" >> $out
      echo "export OCAMLPATH=$OCAMLPATH" >> $out
      echo "export CAML_LD_LIBRARY_PATH=$CAML_LD_LIBRARY_PATH" >> $out
      echo "export OCAMLFIND_DESTDIR=$OCAMLFIND_DESTDIR" >> $out
    '';

in

{
  name = "plutus";

  welcomeMessage = "🤟 \\033[1;34mWelcome to Plutus\\033[0m 🤟";

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
    pkgs.scriv
    pkgs.fswatch
    pkgs.linkchecker

    # Needed to make building things work, not for commands
    pkgs.zlib
    pkgs.cacert

    # Needed for the cabal CLI to download under https
    pkgs.curl

    # Node JS
    pkgs.nodejs_20
  ];


  scripts.assemble-changelog = {
    description = "Assembles the changelog for PACKAGE at VERSION";
    exec = repoRoot.scripts."assemble-changelog.sh";
    group = "changelog";
  };


  scripts.prepare-release = {
    description = "Prepares to release PACKAGEs at VERSION";
    exec = repoRoot.scripts."prepare-release.sh";
    group = "changelog";
  };


  scripts.update-version = {
    description = "Updates the version for PACKAGE to VERSION";
    exec = repoRoot.scripts."update-version.sh";
    group = "changelog";
  };


  shellHook = ''
    ${builtins.readFile certEnv}
  '';

  preCommit = {
    stylish-haskell.enable = true;
    cabal-fmt.enable = true;
    shellcheck.enable = false;
    editorconfig-checker.enable = true;
    nixpkgs-fmt.enable = true;
    optipng.enable = true;
    hlint.enable = false;
  };
}
