{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs;
in

pkgs.stdenv.mkDerivation {
  name = "read-the-docs-site";

  src = pkgs.lib.sourceFilesBySuffices
    (inputs.self + /doc)
    [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];

  buildInputs = [
    inputs.cells.toolchain.packages.sphinx-toolchain
  ];

  dontInstall = true;

  buildPhase = ''
    # FIXME
    # https://input-output.atlassian.net/browse/PLT-789
    # https://hydra.iohk.io/build/18701775/nixlog/1
    mkdir -p $out
    exit 0

    cp -aR ${cell.packages.combined-plutus-haddock}/share/doc haddock
    # -n gives warnings on missing link targets, -W makes warnings into errors
    SPHINX_HADDOCK_DIR=haddock sphinx-build -n -W . $out
    cp -aR haddock $out
  '';
}
