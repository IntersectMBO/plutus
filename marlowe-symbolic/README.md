# Backend for static analysis of Marlowe contracts

This folder contains a symbolic version of the Marlowe semantics written using SBV. Currently, it is able to analyse contracts for potential warnings that could occur in runtime.

The semantics are wrapped in a web-service that answers analysis queries about specific contracts. The web-service takes the contract and an end-point as input and asynchronously answers the query by making an HTTPS request to the endpoint.

## Getting started

The web-service is designed to be deployed as an AWS Lambda. The following command can be used to generate a `.zip` file that can be uploaded to an AWS Lambda:

```bash
nix-build default.nix -A marlowe-symbolic-lambda
```
