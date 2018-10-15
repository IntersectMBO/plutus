-- | A model of the types involved in transactions. These types are intented to
--   be used in PLC scripts.
module Language.Plutus.Runtime (
    -- * Pending transactions
    module Types
    ) where

import           Language.Plutus.Runtime.Types as Types

{- Note [Script types in pending transactions]

To validate a transaction, we have to evaluate the validation script of each of
the transaction's inputs. The validation script sees the data of the
transaction output it validates, and the redeemer of the transaction input of
the transaction that consumes it.

In addition, the validation script also needs information on the transaction as
a whole (not just the output-input pair it is concerned with). This information
is provided by the `PendingTx` type. A `PendingTx` contains the redeemer and
data scripts of all of its inputs and outputs, with types `r` and `d`
respectively. The reason why we are using `r` and `d` instead of `PlcCode` is
that `PendingTx` is intended to be used in PLC scripts only, so we won't create
any values of that type in Haskell (in the coordination code).

This is only a preliminary design and we will have to revisit it later. For
example, it might be desirable to allow a transaction to consume inputs whose
redeemer scripts have different types (in PLC). If that's the case, and we still
want validator scripts to be able to look at all the redeemers, then we would
have to change `pendingTxOtherInputs` to a heterogenous list. (Same for
`pendingTxOutputs`). (This would also affect the "set vs list" question for
transaction inputs -- cf. discussion on
https://github.com/input-output-hk/plutus-prototype/pull/139)

-}

{- Note [Oracles]

I'm not sure how oracles are going to work eventually, so I'm going to use this
definition for now:

* Oracles are identified by their public key
* An oracle can produce "observations", which are values annotated with time
  (block height). These observations are signed by the oracle.
* To use an oracle value inside a validator script, it has to be provided as the
  data script of the transaction that consumes the output locked by the
  validator script.

An example of this can be found in the
Language.Plutus.Coordination.Contracts.Swap.swapValidator script.

-}

{- Note [Transaction Templates]

Transaction templates are currently missing from this mock API and will be
added in the future.

Transaction templates differ from transactions in at least two ways:

1) They do not include a transaction fee (that is, the sum of their input
   values equals the sum of their output values)
2) Part of their input value is not attributed to an address

To turn a template into a transaction, the wallet
1) Adjusts either the input values or the output value to ensure that the
   difference between inputs and outputs matches the transaction fee.
2) Expands the inputs to account for the missing funds (via coin selection).

These two steps depend on each other because the transaction fee is a
function of the size of the transaction including its
inputs.

-}
