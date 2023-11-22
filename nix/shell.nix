{ repoRoot, inputs, pkgs, system, lib }:

cabalProject:

let

  compiler-nix-name = cabalProject.args.compiler-nix-name;
  isGhc98 = lib.hasPrefix "ghc98" compiler-nix-name;

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

    # Needed to make building things work, not for commands
    pkgs.zlib
    pkgs.cacert

    # Needed for the cabal CLI to download under https
    pkgs.curl
  ];

  tools = lib.mkIf isGhc98 {
    # Current HLS doesn't build on 9.8, see https://github.com/input-output-hk/iogx/issues/25
    # This other stuff all depends on HLS.
    haskell-language-server-wrapper = lib.mkForce null;
    haskell-language-server = lib.mkForce null;
    cabal-install = lib.mkForce null;
    stylish-haskell = lib.mkForce null;
    hlint = lib.mkForce null;
  };

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
    # can't do stylish-haskell pre-commit if we don't
    # have stylish-haskell
    stylish-haskell.enable = !isGhc98;
    cabal-fmt.enable = true;
    shellcheck.enable = false;
    editorconfig-checker.enable = true;
    nixpkgs-fmt.enable = true;
    optipng.enable = true;
    hlint.enable = false;
  };
}
