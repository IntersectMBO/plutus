### Added

- CIP-0057 blueprints now carry the names of a data type's constructors and record
  fields. `makeIsDataSchemaIndexed` and `unstableMakeIsDataSchema` populate them from
  the Haskell declaration, so **no annotation is required**: a record's field names
  appear as each field object's `title`, and a constructor's name as its own `title`.
  This is what CIP-0057's normative example shows, and what a consumer needs in order
  to generate typed code from a blueprint.

- `PlutusTx.Blueprint.Schema.FieldSchema`, holding a field's optional name beside its
  schema. The name is merged into the field's own JSON object rather than wrapping it,
  which is the shape the specification uses.

### Changed

- **Breaking:** `ConstructorSchema`'s `fieldSchemas` changed type from
  `[Schema referencedTypes]` to `[FieldSchema referencedTypes]`. Code that constructs a
  `ConstructorSchema` by hand must wrap each field: `MkFieldSchema Nothing schema`
  preserves the previous output, and `MkFieldSchema (Just "name") schema` supplies a
  name. Types whose schema comes from `makeIsDataSchemaIndexed` need no change.

- A constructor's `title` now defaults to the constructor's own name. Previously the
  derivation supplied no title at all, so the variants of a sum type were
  indistinguishable — `Bool`'s two constructors differed only by `index`. An explicit
  `{-# ANN Ctor (SchemaTitle "…") #-}` still takes precedence and is unaffected.

  Blueprints therefore regenerate with additional `title` keys. This is additive: the
  keys are absent from CIP-0057's `constructor` definition, which sets no
  `additionalProperties: false`, so previously-valid blueprints stay valid.
