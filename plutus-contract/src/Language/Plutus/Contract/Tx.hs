{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
module Language.Plutus.Contract.Tx(
      UnbalancedTx
    , emptyTx
    , inputs
    , outputs
    , forge
    , requiredSignatures
    , validityRange
    , mergeWith
    , toLedgerTx
    -- * Constructing transactions
    , unbalancedTx
    , payToScript
    , collectFromScript
    , collectFromScriptFilter
    ) where

import           Control.Lens      (at, (^.))
import qualified Control.Lens.TH   as Lens.TH
import qualified Data.Aeson        as Aeson
import qualified Data.Map          as Map
import           Data.Maybe        (fromMaybe)
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           GHC.Generics      (Generic)

import           Ledger            (Address, DataScript, PubKey, RedeemerScript, TxOut, TxOutRef, ValidatorScript)
import qualified Ledger            as L
import           Ledger.AddressMap (AddressMap)
import qualified Ledger.Interval   as I
import           Ledger.Slot       (SlotRange)
import qualified Ledger.Tx         as Tx
import           Ledger.Value      as V

-- | An unsigned and potentially unbalanced transaction, as produced by
--   a contract endpoint. See note [Unbalanced transactions].
data UnbalancedTx = UnbalancedTx
        { _inputs             :: Set L.TxIn
        , _outputs            :: [L.TxOut]
        , _forge              :: V.Value
        , _requiredSignatures :: [PubKey]
        , _validityRange      :: SlotRange
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

Lens.TH.makeLenses ''UnbalancedTx

-- | An unbalanced transaction wiht no inputs and outputs, and an unbounded
--   validity range.
--
emptyTx :: UnbalancedTx
emptyTx = UnbalancedTx mempty mempty mempty mempty I.always

-- | The ledger transaction of the 'UnbalancedTx'. Note that the result
--   does not have any signatures, and is potentially unbalanced (ie. invalid).
--   To produce a balanced 'Tx', use 'Language.Plutus.Contract.Wallet.balanceTx'.
toLedgerTx :: UnbalancedTx -> L.Tx
toLedgerTx utx = L.Tx
            { L.txInputs = _inputs utx
            , L.txOutputs = _outputs utx
            , L.txForge = _forge utx
            , L.txFee = 0
            , L.txValidRange = _validityRange utx
            , L.txSignatures = Map.empty
            }

-- | Combine two unbalanced transactions by appending their respective inputs,
--   outputs, and signatures, adding their forged values, and applying the
--   given function to their two validity ranges.
mergeWith
    :: (SlotRange -> SlotRange -> SlotRange)
    -> UnbalancedTx
    -> UnbalancedTx
    -> UnbalancedTx
mergeWith f l r = UnbalancedTx
        { _inputs = _inputs l <> _inputs r
        , _outputs = _outputs l <> _outputs r
        , _forge = _forge l `V.plus` _forge r
        , _requiredSignatures = _requiredSignatures l <> _requiredSignatures r
        , _validityRange = f (_validityRange l) (_validityRange r)
        }

-- | Make an unbalanced transaction that does not forge any value. Note that duplicate inputs
--   will be ignored.
unbalancedTx :: [L.TxIn] -> [L.TxOut] -> UnbalancedTx
unbalancedTx ins outs = UnbalancedTx (Set.fromList ins) outs V.zero mempty I.always

-- | Create an `UnbalancedTx` that pays money to a script address.
payToScript :: Value -> Address -> DataScript -> UnbalancedTx
payToScript v a ds = unbalancedTx mempty [outp] where
    outp = Tx.scriptTxOut' v a ds

-- | Create an `UnbalancedTx` that collects script outputs from the
--   address of the given validator script, using the same redeemer script
--   for all outputs. See 'Wallet.API.collectFromScript'.
collectFromScript
    :: AddressMap
    -> ValidatorScript
    -> RedeemerScript
    -> UnbalancedTx
collectFromScript = collectFromScriptFilter (\_ -> const True)

-- | See 'Wallet.API.collectFromScriptFilter'.
collectFromScriptFilter
    :: (TxOutRef -> TxOut -> Bool)
    -> AddressMap
    -> ValidatorScript
    -> RedeemerScript
    -> UnbalancedTx
collectFromScriptFilter flt am vls red =
    let utxo       = fromMaybe Map.empty $ am ^. at (Tx.scriptAddress vls)
        ourUtxo    = Map.toList $ Map.filterWithKey flt utxo
        mkTxIn ref = Tx.scriptTxIn ref vls red
        txInputs   = mkTxIn . fst  <$> ourUtxo
    in
    unbalancedTx txInputs mempty

{- Note [Unbalanced transactions]

To turn an 'UnbalancedTx' into a valid transaction that can be submitted to the
network, the contract backend needs to

* Balance it.
  If the total value of `utxInputs` + the `txForge` field is
  greater than the total value of `utxOutput`, then one or more public key
  outputs need to be added. How many and what addresses they are is up
  to the wallet (probably configurable).
  If the total balance `utxInputs` + the `txForge` field is less than
  the total value of `utxOutput`, then one or more public key inputs need
  to be added (and potentially some outputs for the change).

* Compute fees.
  Once the final size of the transaction is known, the fees for the transaction
  can be computed. The transaction fee needs to be paid for with additional
  inputs so I assume that this step and the previous step will be combined.

  Also note that even if the 'UnbalancedTx' that we get from the contract
  endpoint happens to be balanced already, we still need to add fees to it. So
  we can't skip the balancing & fee computation step.

* Sign it.
  The signing process needs to provide signatures for all public key
  inputs in the balanced transaction, and for all public keys in the
  `utxRequiredSignatures` field.

While there is an 'empty' transaction we can't make 'UnbalancedTx' a monoid
because it's not clear what the binary operator should do with the validity
interval. There are two valid options: Hull and intersection. ('always' is the
unit for the intersection but then there is the issue that we don't have a
canonical representation of the empty interval (that's why 'intersection'
returns a 'Maybe Interval'.))

TODO: Make 'Interval' a lattice

-}
