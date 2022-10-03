{ inputs, cell }@block:
{
  plutus-project = import ./plutus-project.nix block;

  agda-project = import ./agda-project.nix block;

  agda-packages = import ./agda-packages.nix block;
}
