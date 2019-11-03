{ pkgs }:
with pkgs.haskell.lib;
self: super: {
  # Plugins don't work with static compilation. We can stil use the plutus-tx package,
  # we just can't run the tests.
  plutus-tx = dontCheck super.plutus-tx;
}
