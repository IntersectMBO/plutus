{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-
    Event-based interface between contract executables and the app platform and
    (by extension) the wallet.

    Two types of events are defined:

    1. 'ContractOut'. Events produced by the contract for consumption by app
       platform and wallet. Includes transactions and instructions to start
       watching interesting addresses on the ledger.

    2. 'LedgerUpdate'. Events that inform the contract about changes to the
       ledger state.

    Contracts will offer an HTTP interface with the following routes.

    * 1 route per contract endpoint (as defined by contract author)
    * 1 route for submitting 'LedgerUpdate' events

    NOTE: With this design, there are two classes of input events, only one of
          which has a proper data type: Input events from the ledger (in the
          form of 'LedgerUpdate') and input events from the user (in the form
          of HTTP endpoints).

          In my opinion it would be cleaner to add a

          'ContractEndpoint EndpointArgs'

          constructor to 'LedgerUpdate' (and rename the type) that captures all
          contract endpoints activated by the user. I think this will make
          testing a lot easier. But we need to think about the 'EndpointArgs'
          type and how it maps to the actual contract endpoints.
-}
module Language.Plutus.Contract(
    ContractOut(..),
    LedgerUpdate(..),
    UnbalancedTx(..),
    mkUnbalancedTx
    ) where

import qualified Data.Aeson   as Aeson
import           Data.Text    (Text)
import           GHC.Generics (Generic)

import qualified Ledger       as L
import           Ledger.Value as V

-- | An unsigned and potentially unbalanced transaction, as returned by
--   a contract endpoint.
data UnbalancedTx = UnbalancedTx
        { utxInputs  :: [L.TxIn]
        , utxOutputs :: [L.TxOut]
        , utxForge   :: V.Value
        }

        deriving stock (Eq, Ord, Show, Generic)
        deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

-- | Make an unbalanced transaction that does not forge any value.
mkUnbalancedTx :: [L.TxIn] -> [L.TxOut] -> UnbalancedTx
mkUnbalancedTx ins outs = UnbalancedTx ins outs V.zero

{- note [Unbalanced transactions]

To turn an 'UnbalancedTx' into a valid transaction that can be submitted to the
network, the contract backend needs to

* Balance it.
  If the total value of `utxInputs` + the `txForge` field is
  greater than the total value of `utxOutput`, then one or more public key
  outputs need to be added. How many and what addresses they are is up
  to the wallet (probably configurable).
  If the total balance `utxInputs` + the `txForge` field is less than
  the total value of `utxOutput`, then one or more public key inputs need
  to be added (and potentially some outputs for the change)

* Compute fees.
  Once the final size of the transaction is known, the fees for the transaction
  can be computed. The transaction fee needs to be paid for with additional
  inputs so I assume that this step and the previous step will be combined.

  Also note that even if the 'UnbalancedTx' that we get from the contract
  endpoint happens to be balanced already, we still need to add fees to it. So
  we can't skip the balancing & fee computation step.

* Sign it.
  The signing process needs to provide signatures for all public key
  inputs in the balanced transaction.


-}

{- note [ContractFinished event]

The 'ContractFinished' event signals that this *instance* of the contract is
finished. This means that no more interactions with the instance are possible.
It is an opportunity for the contract backend to delete all triggers associated
with the instance, and to update the UI (disable/archive/etc)

Note that the 'ContractFinished' does not say anything about unspent outputs at
the contract address. There may still be unspent outputs at the address, but the
user cannot do anything with them.

For example, the game contract emits a 'ContractFinished' event immediately
after running 'lock' endpoint. So the contract is finished for the initiator of
the game. Participants in the game may still submit guesses etc.

('ContractFinished' seems to be tied closely to contract roles, and we
should think about this some more. This is the difference between the global
(ie. blockchain/utxo set) view and the local (what can that particular role do)
view of a contract.)

-}


-- | Events that are produced by contract endpoints.
data ContractOut =
      SubmitTransaction UnbalancedTx
      -- ^ Produce an 'UnbalancedTx'. See note [Unbalanced transactions]

      | StartWatching L.Address
      -- ^ Start watching an address. This adds the address to the set of
      -- "interesting addresses" of this contract instance.

      | ContractError Text
      -- ^ An error occurred during contract execution.
      --   NOTE: Should we also set the appropriate HTTP status code?

      | ContractFinished
      -- ^ Execution of the contract has ended. No further ledger updates are
      --   required and no user actions are possible. All triggers associated
      --   with this contract instance can be deleted. See note
      --   [ContractFinished event]

      deriving stock (Eq, Ord, Show, Generic)
      deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

-- | Events that inform the contract about changes to the ledger state.
data LedgerUpdate =
    OutputSpent L.TxOutRef L.Tx
    -- ^ An output from one of the interesting addresses was spent. Includes
    --   the transaction that spent the output.
    --   The transaction *spends* the UTXO referenced by 'L.TxOutRef'.

    | OutputAdded L.TxOutRef L.Tx
    -- ^ An output was produced to one of the interesting addresses.
    --   The transaction *produces* the UTXO referenced by 'L.TxOutRef'

    -- NOTE: A transaction that spends an output from an interesting address and
    --       produces a new output to that address will trigger two events:
    --       'OutputSpent' and 'OutputAdded' (with the same 'L.Tx'
    --       argument but with different 'L.TxOutRef' arguments).
    --
    --       TODO: Does it make sense to have a 3rd event type for this
    --       situation?

    | SlotChange L.Slot
    -- ^ The current slot has changed.

    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)
