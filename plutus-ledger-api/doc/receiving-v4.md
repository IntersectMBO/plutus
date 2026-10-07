# Proposed Receiving interface for unfrozen Plutus V4

This changes the draft V4 schema before its freeze. It has not been agreed or
published upstream. Released V1, V2 and V3 interfaces and encodings are unchanged.
The previous V4 `Address` list-product encoding is deliberately replaced; clients
using that draft encoding must update, and validators must be recompiled.

The normal and data-backed interfaces use the following independently fixed Data
constructors. These are Plutus Data indices, distinct from ledger CBOR redeemer
purpose tags even where the proposed numbers happen to coincide.

| Type | Constructor | Data representation |
| --- | --- | --- |
| Address | Address payment account | Constr 0 [payment, account] |
| Address | AddressProtected payment account | Constr 1 [payment, account] |
| ScriptPurpose | Receiving scriptHash | Constr 7 [scriptHash] |
| ScriptInfo | ReceivingScript | Constr 7 [] |

`account` retains V4's `Maybe AccountId` encoding. An AccountId wraps a payment-
style credential; this extension does not introduce V1's StakingCredential or
stake pointers. Existing purpose indices 0 through 6 are unchanged.

The executing Receiving hash is available through `scriptContextScriptHash`, just
as it is for the other V4 purposes. ReceivingScript has no implicit datum. Datums
are inspected through transaction outputs and existing datum witnesses.

`protectedOutputsAt hash txInfo` selects every output at a protected script
address with the supplied hash, returning `(bodyIndex, output)` pairs in authored
order. Unprotected addresses with the same credential are excluded. Indices are
indices in the original body's output list; filtering does not renumber them.
Receiving is grouped by hash in one body. It does not aggregate sibling bodies.

These changes affect context Data only: no new evaluator builtin, cost-model
parameter, script prefix or interpreter instruction is introduced.
