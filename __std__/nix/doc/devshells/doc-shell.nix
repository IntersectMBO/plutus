{ inputs, cell }:

inputs.std.std.lib.mkShell {

  name = "doc-shell";

  imports = [
    inputs.cells.toolchain.devshellProfiles.common
  ];

  packages = [
    cell.library.sphinx-tools
  ];

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
}
