# Building

## Server

``` sh
cd plutus-playground-server
stack build
stack exec -- plutus-playground-server psgenerator ../plutus-playground-client/src/
stack exec -- plutus-playground-server webserver -p 8080 ../plutus-playground-client/dist/
```

## Client

``` sh
cd plutus-playground-client
yarn
yarn run bower install
yarn run webpack
```

## Viewing

Now navigate to the webserver on http://localhost:8080
