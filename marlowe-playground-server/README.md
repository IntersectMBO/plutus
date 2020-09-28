# Marlowe Playground

The Marlowe Playground consists of a Purescript front-end and a Haskell backend. The backend is split into 3 components, [./marlowe-symbolic]() which runs symbolic analysis on Marlowe contracts, [./web-ghc]() which is a web service that runs GHC source code and [./marlowe-playground-server]() which contains other endpoints such as the Actus generators. These components are deployed to different places however a local webserver can be run that makes all these endpoints available on localhost. Due to an implementation detail you currently need to set a few environmental variables, even if they are set to empty strings. Therefore the server can be run with the following command:
```bash
GITHUB_CLIENT_ID="" \
GITHUB_CLIENT_SECRET="" \
JWT_SIGNATURE="" \
GITHUB_REDIRECT_URL="" \
WEBGHC_URL="http://localhost:8080" \
$(nix-build -A marlowe-playground.server-invoker)/bin/marlowe-playground webserver
```

You can now reach the server on [http://localhost:8080]() however you probably want to run the web front-end, see [./marlowe-playground-client/README.md]() for instructions on how to do this.