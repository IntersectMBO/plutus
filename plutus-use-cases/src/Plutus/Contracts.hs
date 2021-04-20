module Plutus.Contracts() where

{- Note [Contracts and Validator Scripts]

Central to both examples are the validator scripts in
`Crowdfunding.contributionScript` and `Swap.swapValidator`. In both cases we
construct a PLC script using the core-to-plutus plugin (with Template Haskell
and the `plc` marker respectively).

The validator scripts currently have a type

Redeemer -> DataValue -> ScriptContext -> a -> ()

Where `a` is a parameter specific to the contract (supplied by the user before
the contract begins). The actual signature of a validator script looks like

Redeemer -> DataValue -> ScriptContext -> ()

So, in the future, the Plutus coordinating code has to translate the `a` value
to PLC and apply it to the function. This could be done with a type class
(similar to aeson's ToJSON).

In order to validate transactions, cardano nodes have to do the same with
`PendingTx` which holds information about the transaction.

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
