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
    pkgs.ghcid

    # Needed to make building things work, not for commands
    pkgs.zlib
    pkgs.cacert

    # Needed for the cabal CLI to download under https
    pkgs.curl

    # Node JS
    pkgs.nodejs_20
  ];

  # Current HLS doesn't build on 9.8, see https://github.com/input-output-hk/iogx/issues/25
  # This other stuff all depends on HLS.
  # FIXME: This is insanely broken somehow. I don't think the module merging is working properly.
  # There is no way to turn off HLS, so I set it to be git. Nonetheless, we somehow end up with
  # a HLS in the 9.8 shell... but a HLS compiled for 9.6.
  tools.haskell-language-server-wrapper =
    lib.mkIf isGhc98 (lib.mkForce pkgs.git);
  tools.haskell-language-server = lib.mkIf isGhc98 (lib.mkForce pkgs.git);
  tools.cabal-install = lib.mkIf isGhc98 (lib.mkForce pkgs.git);
  tools.stylish-haskell = lib.mkIf isGhc98 (lib.mkForce pkgs.git);
  tools.hlint = lib.mkIf isGhc98 (lib.mkForce pkgs.git);

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
