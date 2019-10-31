{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
module Language.Plutus.Contract.Tx(
      UnbalancedTx
    , inputs
    , outputs
    , forge
    , requiredSignatures
    , validityRange
    , toLedgerTx
    , fromLedgerTx
    -- * Constructing transactions
    , unbalancedTx
    , payToScript
    , collectFromScript
    , collectFromScriptFilter
    -- * Constructing inputs
    , Tx.pubKeyTxIn
    , Tx.scriptTxIn
    , Tx.TxOutRefOf(..)
    -- * Constructing outputs
    , Tx.pubKeyTxOut
    , Tx.scriptTxOut
    , Tx.scriptTxOut'
    ) where

import           Control.Lens              (at, (^.))
import qualified Control.Lens.TH           as Lens.TH
import qualified Data.Aeson                as Aeson
import qualified Data.Map                  as Map
import           Data.Maybe                (fromMaybe)
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)

import           Language.PlutusTx.Lattice

import           Ledger                    (Address, DataScript, PubKey, RedeemerScript, TxOut, TxOutRef,
                                            ValidatorScript)
import qualified Ledger                    as L
import           Ledger.AddressMap         (AddressMap)
import           Ledger.Index              (minFee)
import qualified Ledger.Interval           as I
import           Ledger.Slot               (SlotRange)
import qualified Ledger.Tx                 as Tx
import           Ledger.Value              as V

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

instance Pretty UnbalancedTx where
    pretty UnbalancedTx{_inputs, _outputs, _forge, _requiredSignatures, _validityRange} =
        let lines' =
                [ "inputs:" <+> prettyShowList (Set.toList _inputs)
                , "outputs:" <+> prettyShowList _outputs
                , "forge:" <+> pretty _forge
                , "required signatures:" <+> prettyShowList _requiredSignatures
                , "validity range:" <+> viaShow _validityRange
                ]
        in braces $ nest 2 $ vsep lines'

prettyShowList :: Show a => [a] -> Doc ann
prettyShowList = hsep . punctuate comma . fmap viaShow

-- TODO: this is a bit of a hack, I'm not sure quite what the best way to avoid this is
fromLedgerTx :: L.Tx -> UnbalancedTx
fromLedgerTx tx = UnbalancedTx
            { _inputs = L.txInputs tx
            , _outputs = L.txOutputs tx
            , _forge = L.txForge tx
            , _validityRange = L.txValidRange tx
            , _requiredSignatures = Map.keys $ L.txSignatures tx
            }

instance Semigroup UnbalancedTx where
    tx1 <> tx2 = UnbalancedTx {
        _inputs = _inputs tx1 <> _inputs tx2,
        _outputs = _outputs tx1 <> _outputs tx2,
        _forge = _forge tx1 <> _forge tx2,
        _requiredSignatures = _requiredSignatures tx1 <> _requiredSignatures tx2,
        _validityRange = _validityRange tx1 /\ _validityRange tx2
        }

instance Monoid UnbalancedTx where
    mempty = UnbalancedTx mempty mempty mempty mempty top

-- | The ledger transaction of the 'UnbalancedTx'. Note that the result
--   does not have any signatures, and is potentially unbalanced (ie. invalid).
--   To produce a balanced 'Tx', use 'Language.Plutus.Contract.Wallet.balanceTx'.
toLedgerTx :: UnbalancedTx -> L.Tx
toLedgerTx utx =
    let tx = L.Tx
            { L.txInputs = _inputs utx
            , L.txOutputs = _outputs utx
            , L.txForge = _forge utx
            , L.txFee = 0
            , L.txValidRange = _validityRange utx
            , L.txSignatures = Map.empty
            }
     in tx { L.txFee = minFee tx }

-- | Make an unbalanced transaction that does not forge any value. Note that duplicate inputs
--   will be ignored.
unbalancedTx :: [L.TxIn] -> [L.TxOut] -> UnbalancedTx
unbalancedTx ins outs = UnbalancedTx (Set.fromList ins) outs mempty mempty I.always

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
