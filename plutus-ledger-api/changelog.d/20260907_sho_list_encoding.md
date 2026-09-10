### Changed

- Encode product types in the Plutus V4 ledger API as `List` instead of `Constr 0`, including their data-backed counterparts and blueprint schemas. Introduce V4 wrappers for products previously reused from earlier versions, including transaction references, governance products, rational numbers and asset classes. V1-V3 encodings are unchanged.
