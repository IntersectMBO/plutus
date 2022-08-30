{ inputs, cell }@organelle:
{
  sphinx-build-doc-site = import ./sphinx-build-doc-site.nix organelle;

  sphinx-autobuild-doc-site = import ./sphinx-autobuild-doc-site.nix organelle;

  build-and-serve-doc-site = import ./build-and-serve-doc-site.nix organelle;
}