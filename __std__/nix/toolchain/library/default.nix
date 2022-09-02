{ inputs, cell }@organelle:
{
  gitignore-nix = import ./gitignore-nix.nix organelle;
}
