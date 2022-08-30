# A typical good filter for latex sources. This also includes files for cases where
# agda sources are being compiled
{ inputs, cell }:

src: inputs.nixpkgs.lib.sourceFilesBySuffices src
  [ ".tex" ".bib" ".cls" ".bst" ".pdf" ".png" ".agda" ".agda-lib" ".lagda" ]