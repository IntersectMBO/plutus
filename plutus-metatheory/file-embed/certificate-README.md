# Certificate: {{NAME}}

This directory contains a machine-verifiable Agda certificate that
proves the Plutus optimizer correctly transformed a program.
Type-checking this project with Agda verifies the certificate.

## Dependencies

- [Agda](https://agda.readthedocs.io/) 2.8.0
- [Agda standard library](https://github.com/agda/agda-stdlib) 2.3
- [plutus-metatheory](https://github.com/IntersectMBO/plutus/tree/master/plutus-metatheory)

## Type-checking

### Using Nix (recommended)

Enter the development shell provided by the `plutus` repository, `cd` into the root of the certificate project,
and use the bundled Agda wrapper that includes all required libraries:

```
nix develop
agda-with-stdlib-and-metatheory src/{{NAME}}.agda
```

### Without Nix

Ensure Agda 2.8.0 is installed and that both `standard-library-2.3`
and `plutus-metatheory` are registered in your `$AGDA_DIR/libraries`
file (see `plutus-metatheory/AGDA.md` for guidance), then run:

```
agda src/{{NAME}}.agda
```
