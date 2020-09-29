# Marlowe Playground

The Marlowe Playground consists of a Purescript front-end and a Haskell backend. The backend is split into 3 components, [./marlowe-symbolic]() which runs symbolic analysis on Marlowe contracts, [./web-ghc]() which is a web service that runs GHC source code and [./marlowe-playground-server]() which contains other endpoints such as the Actus generators. These components are deployed to different places however a local webserver can be run that makes all these endpoints available on localhost. The server can be run with the following command:
```bash
$(nix-build -A marlowe-playground.server-invoker)/bin/marlowe-playground webserver
```

You can now reach the server on [http://localhost:8080]() however you probably want to run the web front-end, see [./marlowe-playground-client/README.md]() for instructions on how to do this.