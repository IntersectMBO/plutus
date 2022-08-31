{ inputs, cell }@organelle:
{
  sphinx-build-doc-site = import ./sphinx-build-doc-site.nix organelle;

  sphinx-autobuild-doc-site = import ./sphinx-autobuild-doc-site.nix organelle;

  serve-readthedocs-site = import ./serve-readthedocs-site.nix organelle;
}
