# This builds a vscode devcontainer that can be used with the plutus-starter project (or probably the plutus project itself).
{ pkgs, plutus }:
let
  shell = (plutus.haskell.project.shellFor { withHoogle = false; });
  # This is an evil hack to allow us to have a docker container with a "similar" environment to
  # our haskell.nix shell without having it actually run nix-shell. In particular, we need some
  # of the flags that the stdenv setup hooks set based on the build inputs, like NIX_LDFLAGS.
  # The result of this derivation is a file that can be sourced to set the variables we need.
  horrible-env-vars-hack = pkgs.runCommand "exfiltrate-env-vars"
    {
      inherit (shell) buildInputs nativeBuildInputs propagatedBuildInputs;
    } ''
    set | grep -v -E '^BASHOPTS=|^BASH_VERSINFO=|^EUID=|^PPID=|^SHELLOPTS=|^UID=|^HOME=|^TEMP=|^TMP=|^TEMPDIR=|^TMPDIR=|^NIX_ENFORCE_PURITY=' >> $out
  '';
in
pkgs.callPackage (import ./devcontainer.nix) {
  name = "plutus-devcontainer";
  tag = "latest";
  extraContents = [
    shell.ghc
    plutus.haskell-language-server
    plutus.cabal-install
    pkgs.binutils
  ];
  extraCommands = ''
    # Put the environment stuff somewhere convenient
    chmod +w etc
    mkdir -p etc/profile.d
    echo 'set -o allexport' >> etc/profile.d/env.sh
    echo 'source ${horrible-env-vars-hack}' >> etc/profile.d/env.sh
    echo 'set +o allexport' >> etc/profile.d/env.sh

    # We just clobbered this, put it back
    echo 'export PATH=$PATH:/usr/bin:/bin' >> etc/profile.d/env.sh
    echo 'export NIX_BUILD_TOP=$(mktemp -d)' >> etc/profile.d/env.sh

    # Load all the stuff in an interactive session too
    chmod +w root
    echo 'source /etc/profile.d/env.sh' >> root/.bashrc
  '';
}
