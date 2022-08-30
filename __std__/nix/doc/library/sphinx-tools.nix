{ inputs, cell }:

inputs.nixpkgs.python3.withPackages (pkgs: [

  inputs.cells.toolchain.packages.sphinxcontrib-haddock
  inputs.cells.toolchain.packages.sphinxcontrib-domaintools
  inputs.cells.toolchain.packages.sphinx-markdown-tables
  inputs.cells.toolchain.packages.sphinxemoji

  pkgs.sphinxcontrib_plantuml
  pkgs.sphinxcontrib-bibtex
  pkgs.sphinx-autobuild
  pkgs.sphinx
  pkgs.sphinx_rtd_theme
  pkgs.recommonmark
])
