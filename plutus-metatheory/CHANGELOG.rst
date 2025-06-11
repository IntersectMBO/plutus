
.. _changelog-1.47.0.0:

1.47.0.0 — 2025-06-10
=====================

# Added

Initial Translation Relation for the Untyped Case of Case simplification phase

Added
-----

 - Support for all V2 builtin-functions for UPLC (mode U)

- Switch from `cryptonite` library to `crypton` (a drop in replacement).

- Failed certifications now produce counterexamples

- The certifier component has been moved from `plutus-executables` to `plutus-metatheory`. It has also been exposed as a library inside the package.

Changed
-------

- Certificates now are generated as Agda projects, and the UPLC ASTs are deduplicated to greatly reduce the size of the certificates.

Fixed
-----

- Deciding equality between builtins no longer gets stuck.

- Fixed the runtime representation of `VerifiedCompilation.Equality.builtinEq`.
- `DATA` equality now depends on `builtinEq` as well.

- Fixed a few Agda unparsing issues which were causing syntax errors in the certifier's generated certificates.
