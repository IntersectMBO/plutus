{ inputs, cell }:

inputs.std.lib.dev.mkShell {

  name = "doc-shell";

  imports = [
    inputs.cells.toolchain.devshellProfiles.common
  ];

  packages = [
    inputs.cells.toolchain.packages.sphinx-toolchain
  ];

  commands = [
    {
      package = cell.scripts.sphinx-build-readthedocs-site;
      category = "doc";
      help = "Build the docs locally with output in doc/_build";
    }
    {
      package = cell.scripts.sphinx-autobuild-readthedocs-site;
      category = "doc";
      help = "Start the autobuild server with output in doc/_build";
    }
    {
      package = cell.scripts.serve-readthedocs-site;
      category = "doc";
      help = "nix build and serve the doc site on port 3000";
    }
  ];
}
