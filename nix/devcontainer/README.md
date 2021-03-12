Skeleton of a devcontainer for working on Plutus projects, based on https://github.com/hamishmack/docker-nixpkgs/blob/hkm/nix-devcontainer/images/devcontainer with some tweaks.
The main derivation is in `default.nix` in the root, since it needs to add some extra things.

Usage:
1. `docker load < $(nix-build default.nix -A devcontainer)`
2. Create `.devcontainer/devcontainer.json` in your project as below, the "image" property is most important
3. Install the Remote Development extension pack in VSCode
4. Open the folder "in the container"

Example `devcontainer.json`:
```
{
    "name": "My Plutus Project",
    "image": "plutus-devcontainer:latest",

    // Use 'settings' to set *default* container specific settings.json values on container create.
    // You can edit these settings after create using File > Preferences > Settings > Remote.
    "settings": {
        "terminal.integrated.shell.linux": "/bin/bash"
    },

    // IDs of extensions inside container.
    "extensions": [
        "haskell.haskell"
    ],
}
```
