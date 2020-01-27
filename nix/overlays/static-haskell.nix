{ pkgs }:
with pkgs.haskell.lib;
self: super: {
  # Plugins don't work with static compilation. We can stil use the plutus-tx-plugin package,
  # we just can't run the tests.
  plutus-tx-plugin = dontCheck super.plutus-tx-plugin;
}
