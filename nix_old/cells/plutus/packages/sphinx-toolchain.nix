{ inputs, cell }:

cell.library.pkgs.python3.withPackages (pkgs: [

  cell.packages.sphinxcontrib-haddock
  cell.packages.sphinxcontrib-domaintools
  cell.packages.sphinxcontrib-bibtex
  cell.packages.sphinx-markdown-tables
  cell.packages.sphinxemoji

  pkgs.sphinxcontrib_plantuml
  pkgs.sphinx-autobuild
  pkgs.sphinx
  pkgs.sphinx_rtd_theme
  pkgs.recommonmark
])
