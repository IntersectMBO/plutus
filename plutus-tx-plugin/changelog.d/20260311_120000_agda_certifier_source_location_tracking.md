### Added

- `certify` plugin option to trigger Agda certificate generation for compiled
  Plutus scripts. Each certificate is written to a directory named
  `<package>_<module>-<hash>.agda-cert`, where `<hash>` is a random 6-char
  alphanumeric tag.
- `generateCertificate` top-level function that invokes the certifier with
  package and module names.
