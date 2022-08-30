{ inputs, cell }:

inputs.nixpkgs.stdenv.mkDerivation {
  name = "plutus-docs";

  src = inputs.nixpkgs.lib.sourceFilesBySuffices
    (inputs.self + /doc)
    [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];

  buildInputs = [
    cell.library.sphinx-tools
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
