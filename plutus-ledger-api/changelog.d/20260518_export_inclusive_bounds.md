### Added

- Exported `inclusiveLowerBound` and `inclusiveUpperBound` from
  `PlutusLedgerApi.V1.Interval`, `PlutusLedgerApi.V1.Data.Interval`,
  and all re-exporting modules (`PlutusLedgerApi.V1`/`V2`/`V3` and the
  `PlutusLedgerApi.Data.V1`/`V2`/`V3` counterparts). These helpers
  normalise `LowerBound`/`UpperBound` values into an equivalent
  inclusive `Extended a`, removing the need for validator authors to
  re-implement the same closure handling locally.
