# Building

## Server

### stack

```sh
cd plutus-playground-server
cp playground.yaml.sample playground.yaml

vi playground.yaml # Fill in this file.

stack build
stack exec -- plutus-playground-server psgenerator ../plutus-playground-client/src/
stack exec -- plutus-playground-server webserver ../plutus-playground-client/dist/
```

### nix

```sh
nix build -f default.nix plutus-playground.server-invoker 
result/bin/plutus-server-invoker webserver -p 4000 ./plutus-playground/plutus-playground-client/dist
```

## Client

```sh
cd plutus-playground-client
yarn
yarn run bower install
```

Then run `yarn run webpack:server` for an auto-reloading dev build on https://localhost:8009

You may also want to run `yarn run purs:ide` to start `psc-ide`
support running with the correct paths.

## nix

Fair warning before we start: You may struggle with PureScript on Nix on OSX.

The client and server can be built from the top-level of this repo with:

```sh
nix-build \
  --option trusted-public-keys "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" \
  --option substituters https://hydra.iohk.io \
  -A plutus-playground.client -A plutus-playground.server-invoker
```

(You may prefer to put those option flags in your global =nix.conf= file.)

When the client's dependencies change you may need to update the nix packages scripts for yarn and bower:

```sh
cd plutus-playground/plutus-playground-client
nix-shell -p yarn2nix --run 'yarn2nix | tee yarn.nix'
nix-shell -p nodePackages.bower2nix --run 'bower2nix | tee bower-packages.nix'
```

## Docker image

```sh
nix build -f default.nix plutus-playground.docker
docker load < result
# You can see the image name and tag as a result of the previous command and use it below
docker run -p 8080:8080 plutus-playground-docker:somecrazytag
```

# Troubleshooting

On a Mac, you may see this when compiling a contract:

```
GhcException "unable to load package `integer-gmp-1.0.2.0'"
```

This is due to a [GHC
bug](https://ghc.haskell.org/trac/ghc/ticket/15105). Sadly this isn't
slated to be fixed until GHC 8.8 at the earliest, but there's a simple
workaround (listed in that ticket):

``` sh
find ~/.stack -name HSinteger-gmp-1.0.2.0.o -ok rm {} \;
```
