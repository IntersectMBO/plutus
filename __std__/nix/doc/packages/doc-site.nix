{ inputs, cell }:

inputs.nixpkgs.stdenv.mkDerivation {
  name = "plutus-docs";

  src = inputs.nixpkgs.lib.sourceFilesBySuffices 
    (inputs.self + /doc) 
    [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];
  
  buildInputs = [
    
    inputs.cells.toolchain.packages.sphinxcontrib-haddock
    inputs.cells.toolchain.packages.sphinxcontrib-domaintools
    inputs.cells.toolchain.packages.sphinx-markdown-tables
    inputs.cells.toolchain.packages.sphinxemoji

    inputs.nixpkgs.python3Packages.sphinx
    inputs.nixpkgs.python3Packages.sphinx_rtd_theme
    inputs.nixpkgs.python3Packages.sphinxcontrib_plantuml
    inputs.nixpkgs.python3Packages.sphinxcontrib-bibtex
    inputs.nixpkgs.python3Packages.recommonmark
  ];

  dontInstall = true;

  # TODO(std) cannot be built untile we std'ize the haskell packages.
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