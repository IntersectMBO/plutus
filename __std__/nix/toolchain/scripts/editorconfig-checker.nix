{ inputs, cell }:

# Runs `editorconfig-checker` on ${src}. If there are errors,
# TODO(std) original line:
# they are written to `$out/nix-support/hydra-build-products`
# TODO(std) new line: (which is right?)
# they are written to `$out/nix-support/editorconfig-checker.log`
inputs.nixpkgs.stdenv.mkDerivation {
  name = "editorconfig-checker";
  
  src = inputs.cells.toolchain.packages.gitignore-nix.gitignoreSource inputs.self;
  
  buildInputs = [inputs.nixpkgs.editorconfig-checker];

  installPhase = ''
    mkdir -p "$out/nix-support"

    set -e
    # changing to the directory and then running it gives better output than
    # passing the directory to check, since file names are shorter
    cd $src
    editorconfig-checker 2>&1 | tee "$out/nix-support/editorconfig-checker.log"

    if [ $? -ne 0 ]; then
      echo "*** editorconfig-checker found files that don't match the configuration"
      exit 1
    fi
  '';
}
