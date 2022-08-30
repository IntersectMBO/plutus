{ inputs, cell }:

let 
  sphinxTools = inputs.nixpkgs.python3.withPackages (pkgs: [

    inputs.cells.toolchain.packages.sphinxcontrib-domaintools
    inputs.cells.toolchain.packages.sphinx-markdown-tables
    inputs.cells.toolchain.packages.sphinxemoji

    pkgs.sphinxcontrib_plantuml
    pkgs.sphinxcontrib-bibtex
    pkgs.sphinx-autobuild
    pkgs.sphinx
    pkgs.sphinx_rtd_theme
    pkgs.recommonmark
  ]);

in 

inputs.std.std.lib.mkShell {
  name = "doc-shell";
  imports = [inputs.cells.toolchain.devshellProfiles.common];
  commands = [
    {
      package = cell.scripts.sphinx-build-doc-site;
      category = "doc";
      help = "Build the docs locally in doc/_build";
    }
    {
      package = cell.scripts.sphinx-autobuild-doc-site;
      category = "doc";
      help = "Start the autobuild server in doc/_build";
    }
    {
      package = cell.scripts.build-and-serve-doc-site;
      category = "doc";
      help = "Full nix build of the doc + serve them on port 3000";
    }
  ];
  packages = [ sphinxTools ];
}