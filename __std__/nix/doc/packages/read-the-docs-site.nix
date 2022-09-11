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

  # TODO(std) needs haskell-nix
  buildPhase = ''
    echo FIXME > $out && exit 0 

    cp -aR ${cell.packages.combined-plutus-haddock}/share/doc haddock
    # -n gives warnings on missing link targets, -W makes warnings into errors
    SPHINX_HADDOCK_DIR=haddock sphinx-build -n -W . $out
    cp -aR haddock $out
  '';
}
