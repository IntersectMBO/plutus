### Changed

- `CannotParseValue` plugin-option parse error now carries a human-readable
  detail string instead of a placeholder `SomeTypeRep`. Errors produced by
  `plcParserOption` include the underlying parser error message (source
  position and explanation), so failures to parse option values are no
  longer reported as "into type Int".
