# Changed

- Change the unfrozen Plutus V4 Address Data format from a positional list product
  to indexed ordinary `Address` (constructor 0) and protected `AddressProtected`
  (constructor 1) forms. Both preserve the existing `Maybe AccountId` staking
  representation. Clients of the previous draft V4 format must update and V4
  validators must be recompiled. Released V1-V3 formats are unchanged.

# Added

- Add Receiving `ScriptPurpose` and `ReceivingScript` `ScriptInfo` to normal and
  data-backed V4 interfaces, both at Data constructor index 7. `Receiving
  ScriptHash Integer` identifies one protected output by its original body index;
  `ReceivingScript Integer TxOut` exposes that index and the exact resolved output.
  Identical outputs at different indexes require separate executions and
  redeemers. Receiving has no implicit datum argument and uses the existing
  `scriptContextScriptHash` field. Purpose and script-info encodings 0-6 retain
  their existing fields and order.
- Add `protectedOutputsAt`, which selects every protected script output for a
  recipient while retaining authored body output indexes. Payment and account
  inspection helpers also recognize protected addresses.
