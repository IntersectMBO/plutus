{ inputs, cell }@organelle:
{
  sphinx-build-readthedocs-site = import ./sphinx-build-readthedocs-site.nix organelle;

  sphinx-autobuild-readthedocs-site = import ./sphinx-autobuild-readthedocs-site.nix organelle;

  serve-readthedocs-site = import ./serve-readthedocs-site.nix organelle;
}
