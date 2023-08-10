# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#35-nixper-system-outputsnix

{ nix, projects, ... }:

{
  documents = nix.plutus.latex-docs;

  packages.plutus-metatheory-site = nix.plutus.plutus-metatheory-site;

  # Needed by .github/workflows/hlint.yml
  hlint = projects.default.hsPkgs.hlint.components.exe.hlint;
}
