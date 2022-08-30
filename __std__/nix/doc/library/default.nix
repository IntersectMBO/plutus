{ inputs, cell }@organelle:
{
  build-latex-doc = import ./build-latex-doc.nix organelle;

  build-latex = import ./build-latex.nix organelle;

  filter-latex-sources = import ./filter-latex-sources.nix organelle;

  sphinx-tools = import ./sphinx-tools.nix organelle;
}


