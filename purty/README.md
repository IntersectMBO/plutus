# Purty

Currently Purty is a little difficult to build with nix for two reasons:

* It uses purescript 0.13.2 which requires a newer version of `network` than is in stackage. Since other packages have version bounds on `network` we must use `jailbreak = true` for `purescript`.
* `stack2nix` makes a mistake when generating `hfsevents` and does not include `CoreServices` in the arguments to `callPackage`.

For these reasons we build purty with it's own packages.nix file and overrides rather than including it in the main plutus packages. We hope to put it back in later on but since it's a bit bleeding edge at the moment I think this is to be expected.

## Upgrading

To upgrade purty, change the `purtySrc` definition to the correct revision then `git clone https://gitlab.com/joneshf/purty.git` somewhere. You will need to make sure that the following `extra-deps` are in the `stack.yaml` file:
```
  - socks-0.6.0
  - connection-0.3.0
```
This is required to make sure `stack2nix` uses the correct version of these libraries.

Now you can run:
```
nix-shell -p stack2nix
stack2nix . > packages.nix
```
Then move the generated `packages.nix` to this directory.