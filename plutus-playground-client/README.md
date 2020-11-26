# Building

## Server

Please view the instructions for building the server [here](../plutus-playground-server/README.md).

## Client

```sh
# First generate the purescript bridge files
$(nix-build -A plutus-playground.server-invoker)/bin/plutus-playground psgenerator ./plutus-playground-client/generated
# Now we will build and run the client on localhost
cd plutus-playground-client
# Download javascript dependencies
npm install
# Install purescript depdendencies
npm run purs:compile
```

Then run `npm run webpack:server` for an auto-reloading dev build on https://localhost:8009

You may also want to run `npm run purs:ide` to start `psc-ide`
support running with the correct paths.

## Adding dependencies

* Javascript dependencies are managed with npm, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change `psc-package.json` or `packages.dhall` you need to make sure that all dependencies can still properly be resolved and built.
You can do so using the `update-client-deps` script:

- Inside the nix-shell environment: `update-client-deps`
- Outside of the nix-shell environment (from the client directory): `$(nix-build -A plutus.updateClientDeps ../)/bin/update-client-deps`

The `update-client-deps` script will generate/update `.nix` files which have to be committed and are required for a successful CI run.

### NodeJS GitHub dependencies

All npm dependencies are handled by npmlock2nix automatically and transparently. The only exception to this rule are GitHub dependencies.
In order for these to work in restricted evaluation mode (which is what hydra uses) you have to specify the sha256 of the dependency you
want to use in your `buildNodeModules`. For example:

```
buildNodeModules {
    projectDir = ./.;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = {
      shmish111.nearley-webpack-loader."939360f9d1bafa9019b6ff8739495c6c9101c4a1" = "1brx669dgsryakf7my00m25xdv7a02snbwzhzgc9ylmys4p8c10x";
    };
}
```

You can add new dependencies with the sha256 set to `"0000000000000000000000000000000000000000000000000000"`. This will yield an error
message during the build with the actual hash value.

## nix

Fair warning before we start: You may struggle with PureScript on Nix on OSX.

The client and server can be built from the top-level of this repo with:

When building the client make sure that the generated directory is removed completely or you will get _Duplicate module_ errors.

```sh
nix-build \
  --option trusted-public-keys "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" \
  --option substituters https://hydra.iohk.io \
  -A plutus-playground.client -A plutus-playground.server-invoker
```

(You may prefer to put those option flags in your global =nix.conf= file.)

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
