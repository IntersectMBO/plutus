# Changed

- Change the unfrozen Plutus V4 Address Data format from a positional list product
  to indexed ordinary `Address` (constructor 0) and protected `AddressProtected`
  (constructor 1) forms. Both preserve the existing `Maybe AccountId` staking
  representation. Clients of the previous draft V4 format must update and V4
  validators must be recompiled. Released V1-V3 formats are unchanged.

# Added

- Add Receiving `ScriptPurpose` and `ReceivingScript` `ScriptInfo` to normal and
  data-backed V4 interfaces, both at Data constructor index 7. Receiving authorizes
  protected outputs for the executing hash in one transaction body; it has no
  implicit datum and uses the existing `scriptContextScriptHash` field.
- Add `protectedOutputsAt`, which selects every protected script output for a
  recipient while retaining authored body output indexes. Payment and account
  inspection helpers also recognize protected addresses.
