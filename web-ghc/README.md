# Building

## Server

### stack

```sh
cd playground-server
cp playground.yaml.sample playground.yaml

vi playground.yaml # Fill in this file.

stack build
stack exec web-ghc-server -- webserver
```

### nix

```sh
nix build -f default.nix web-ghc
./result/bin/web-ghc-server webserver
```