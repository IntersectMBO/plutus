# Plutus example project

## Getting started

The following should work on any machine that has nix installed however if you wish to avoid any problems you can setup a NixOS virtual machine, see the [NixOS section](#nixos) for more info.

```bash
# The plutus project contains this example project
git clone https://github.com/input-output-hk/plutus.git

# copy the project for yourself
cp -r plutus/example my-example
cd my-example

# We use a nix shell to ensure all tools and paths are set up correctly
nix-shell

# update cabal for the first time
cabal new-update

# On some systems (e.g. NixOS) you need to tell cabal where some system libraries are
# for example openssl. You can do this either in ~/.cabal/config or cabal.project.local
# Just add the line `extra-lib-dirs: /run/current-system/sw/lib` to one of those files
# Alternatively you can use the following command to add this to ~/.cabal/config
# cabal user-config update -a "extra-lib-dirs: /run/current-system/sw/lib"

# build the project
cabal new-build

# install the haskell extension for vs code
code --install-extension alanz.vscode-hie-server

# launch vs code from this nix-shell
# You must run `code` from within the nix shell in order for Haskell IDE Engine to work correctly
code
```

## NixOS

This directory also includes a `configuration.nix` file which can be used in a NixOS installation. This makes sure the correct system libraries are available as well as adding the Haskell IDE Engine cachix nix cache. This `configuration.nix` file can be used on a clean NixOS installation and everything will just work.

You can use this to easily setup a Virtual Box VM:

1. download the VirtualBox appliance from https://nixos.org/nixos/download.html
2. import the appliance
3. before starting the VM make sure you give it plenty of memory, 6Gb should be plenty
4. start the machine
5. run `sudo -i` with password `demo`
6. replace `/etc/nixos/configuration.nix` with the file in this directory
7. run `nixos-rebuild switch`
8. run `exit` to get back to the demo user shell