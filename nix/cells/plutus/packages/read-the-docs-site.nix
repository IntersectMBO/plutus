{ inputs, cell }:

let
  inherit (cell.library) pkgs;
in

pkgs.stdenv.mkDerivation {
  name = "read-the-docs-site";

  src = pkgs.lib.sourceFilesBySuffices
    (inputs.self + /doc/read-the-docs-site)
    [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];

  buildInputs = [
    cell.packages.sphinx-toolchain
    # We need this here in order to get the `plantuml` executable in PATH.
    # Unfortunately `python3.withPackages` (used by cell.packages.sphinx-toolchain above)
    # won't do it automatically.
    pkgs.python3Packages.sphinxcontrib_plantuml
  ];

  dontInstall = true;

  # TODO(std) fix me after fixing combined-plutus-haddock
  # cp -aR ${cell.packages.combined-plutus-haddock}/share/doc haddock
  buildPhase = ''
    mkdir -p $out
    touch $out/TODO
    exit 0

    # -n gives warnings on missing link targets, -W makes warnings into errors
    SPHINX_HADDOCK_DIR=haddock sphinx-build -n -W . $out
    cp -aR haddock $out
  '';
}
