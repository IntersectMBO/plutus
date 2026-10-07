# Proposed Receiving interface for unfrozen Plutus V4

This changes the draft V4 schema before its freeze. Upstream agreement remains
pending. Released V1, V2 and V3 interfaces and encodings are unchanged.
The previous V4 `Address` list-product encoding is deliberately replaced; clients
using that draft encoding must update, and validators must be recompiled.

The normal and data-backed interfaces use the following independently fixed Data
constructors. These are Plutus Data indices, distinct from ledger CBOR redeemer
purpose tags even where the proposed numbers happen to coincide.

| Type | Constructor | Data representation |
| --- | --- | --- |
| Address | Address payment account | Constr 0 [payment, account] |
| Address | AddressProtected payment account | Constr 1 [payment, account] |
| ScriptPurpose | Receiving scriptHash outputIndex | Constr 7 [scriptHash, outputIndex] |
| ScriptInfo | ReceivingScript outputIndex resolvedOutput | Constr 7 [outputIndex, resolvedOutput] |

`account` retains V4's `Maybe AccountId` encoding. An AccountId wraps a payment-
style credential; this extension does not introduce V1's StakingCredential or
stake pointers. Existing purpose indices 0 through 6 are unchanged.

The executing Receiving hash is available through `scriptContextScriptHash`, just
as it is for the other V4 purposes. Each protected Plutus script output requires
its own Receiving execution and redeemer. Native scripts retain phase-1
authorization and require no Plutus Receiving redeemer. `outputIndex` is the
zero-based index in the original body's complete output list. Ordinary outputs and outputs for other
scripts still occupy their original slots; filtering does not renumber indexes.
Identical protected outputs at different slots therefore have distinct purposes.

`ReceivingScript` exposes the exact resolved output for this execution. It has no
implicit datum argument: a validator inspects `resolvedOutput` and existing datum
witnesses. The surrounding `TxInfo` still contains all outputs for the current
body. Top-level and child bodies keep separate output-index domains.

`protectedOutputsAt hash txInfo` selects every output at a protected script
address with the supplied hash, returning `(bodyIndex, output)` pairs in authored
order. Unprotected addresses with the same credential are excluded. Indices are
indices in the original body's output list; filtering does not renumber them.
This helper is an optional query over transaction outputs, not the execution
domain: Receiving executes once per protected Plutus script output, even when
several outputs have the same hash.

These changes affect context Data only: no new evaluator builtin, cost-model
parameter, script prefix or interpreter instruction is introduced.
