{ inputs, cell }:

# TODO(std)
{
  haskellLib = {
    collectComponents' = _: _: { };
  };

  cabalProject' = _: {};

  hackage-project = _: {};
}
