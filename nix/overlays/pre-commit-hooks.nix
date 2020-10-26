self: super:
{
  nix-pre-commit-hooks = import ((import ../sources.nix)."pre-commit-hooks.nix");
}
