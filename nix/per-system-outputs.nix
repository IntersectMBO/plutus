# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#35-nixper-system-outputsnix

{ nix, ... }:

{
  documents = nix.plutus.latex-docs;

  packages.plutus-metatheory-site = nix.plutus.plutus-metatheory-site;
}
