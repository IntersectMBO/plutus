module Language.PlutusTx.Coordination.Contracts(
  -- * Example contracts
  module CrowdFunding,
  module Swap,
  module Vesting
  ) where

import           Language.PlutusTx.Coordination.Contracts.CrowdFunding as CrowdFunding
import           Language.PlutusTx.Coordination.Contracts.Swap         as Swap
import           Language.PlutusTx.Coordination.Contracts.Vesting      as Vesting

{- Note [Contracts and Validator Scripts]

Central to both examples are the validator scripts in
`CrowdFunding.contributionScript` and `Swap.swapValidator`. In both cases we
construct a PLC script using the core-to-plutus plugin (with Template Haskell
and the `plc` marker respectively).

The validator scripts currently have a type

Redeemer -> DataScript -> PendingTx -> a -> ()

Where `a` is a parameter specific to the contract (supplied by the user before
the contract begins). The actual signature of a validator script looks like

Redeemer -> DataScript -> PendingTx -> ()

So, in the future, the Plutus coordinating code has to translate the `a` value
to PLC and apply it to the function. This could be done with a type class
(similar to aeson's ToJSON).

In order to validate transactions, cardano nodes have to do the same with
`PendingTx` which holds information about the transaction.

-}
