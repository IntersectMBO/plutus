{ inputs, cell }:

inputs.nixpkgs.stdenv.mkDerivation {
  name = "read-the-docs-site";

  src = inputs.nixpkgs.lib.sourceFilesBySuffices
    (inputs.self + /doc)
    [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];

  buildInputs = [
    inputs.cells.toolchain.packages.sphinx-toolchain
  ];

  dontInstall = true;

  # TODO(std) cannot be built until we std'ize the haskell packages.
  # Original:
  # cp -aR ${plutus.plutus-haddock-combined}/share/doc haddock
  # -n gives warnings on missing link targets, -W makes warnings into errors
  # SPHINX_HADDOCK_DIR=haddock sphinx-build -n -W . $out
  # cp -aR haddock $out
  buildPhase = ''
    mkdir -p $out
    touch $out/todo
  '';
}
