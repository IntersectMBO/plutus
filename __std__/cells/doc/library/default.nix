{ inputs, cell }@block:
{
  build-latex-doc = import ./build-latex-doc.nix block;

  build-latex = import ./build-latex.nix block;

  filter-latex-sources = import ./filter-latex-sources.nix block;
}


