{ inputs, cell }@block:
{

  sphinx-build-readthedocs-site = import ./sphinx-build-readthedocs-site.nix block;

  sphinx-autobuild-readthedocs-site = import ./sphinx-autobuild-readthedocs-site.nix block;

  serve-readthedocs-site = import ./serve-readthedocs-site.nix block;

}
