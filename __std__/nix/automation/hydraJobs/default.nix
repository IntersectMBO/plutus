{ inputs, cell }@block: rec
{
  default = required-jobset;

  required-jobset = import ./required-jobset.nix block;
}
