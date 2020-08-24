# Building

## Server

### stack

```sh
stack build
stack exec web-ghc-server -- webserver
```

### nix

```sh
nix build -f default.nix web-ghc
./result/bin/web-ghc-server webserver
```