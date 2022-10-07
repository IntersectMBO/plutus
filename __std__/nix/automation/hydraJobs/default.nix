{ inputs, cell }@block: rec
{
  all = import ./all.nix block;
}
