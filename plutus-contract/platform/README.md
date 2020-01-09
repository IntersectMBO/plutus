This directory contains platform-specific code for starting up
a contract.

Each contract is a Haskell program that behaves in a certain way
to allow the contract loader in the wallet to start the contract and
interact with it.

We have the following platforms

### Network

The contract is compiled to an executable that starts an HTTP server
that exposes the contract functionality.

See the source code comments for details on how to specify the listen
address and port.

### Web

The contract is loaded into a JavaScript engine and a JavaScript API
is used to access the contract functionality.

See the source code comments for how to use the JavaScript API.
