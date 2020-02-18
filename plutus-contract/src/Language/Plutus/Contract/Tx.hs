{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
module Language.Plutus.Contract.Tx(
      UnbalancedTx
    , toLedgerTx
    , fromLedgerTx
    -- * Constructing transactions
    , payToScript
    , payToPubKey
    , payToPubKeyHash
    , collectFromScript
    , collectFromScriptFilter
    , forgeValue
    , moveValue
    , mustBeValidIn
    , mustBeSignedBy
    , mustSpendInput
    , mustProduceOutput
    , mustIncludeDataValue
    -- * Inspecting 'UnbalancedTx' values
    , valueMoved
    , requiredSignatories
    , validityRange
    -- * Inspecting 'UnbalancedTx' constraints
    , modifiesUtxoSet
    , hasValidTx
    -- * Constructing inputs
    , Tx.pubKeyTxIn
    , Tx.scriptTxIn
    , Tx.TxOutRef(..)
    -- * Constructing outputs
    , Tx.pubKeyTxOut
    , Tx.pubKeyHashTxOut
    , Tx.scriptTxOut
    , Tx.scriptTxOut'
    ) where

import qualified Data.Aeson                as Aeson
import           Data.Foldable             (toList)
import qualified Data.Map                  as Map
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)

import           Language.PlutusTx.Lattice

import           IOTS                      (IotsType)
import           Ledger                    (Address, DataValue, PubKey, PubKeyHash, RedeemerValue, TxOutRef, TxOutTx,
                                            Validator)
import qualified Ledger                    as L
import           Ledger.AddressMap         (AddressMap)
import           Ledger.Index              (minFee)
import qualified Ledger.Interval           as I
import           Ledger.Slot               (SlotRange)
import qualified Ledger.Tx                 as Tx
import           Ledger.Value              as V

import qualified Wallet.API                as WAPI

-- | An unsigned and potentially unbalanced transaction, as produced by
--   a contract endpoint. See note [Unbalanced transactions].
data UnbalancedTx = UnbalancedTx
        { _inputs              :: Set L.TxIn
        , _outputs             :: [L.TxOut]
        , _forge               :: V.Value
        , _forgeScripts        :: Set L.MonetaryPolicy
        , _requiredSignatories :: [PubKeyHash]
        , _dataValues          :: [DataValue]
        , _validityRange       :: SlotRange
        , _valueMoved          :: Value
        -- ^ The minimum size of the transaction's left and right side. The
        --   purpose of this field is to enable proof of ownership for tokens
        --   (a transaction proves ownership of a token if the value consumed
        --   and spent by it includes the token. The value in the '_valueMoved'
        --   field will be paid from the wallet's own funds back to an address
        --   owned by the wallet)
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (Aeson.FromJSON, Aeson.ToJSON, IotsType)

instance Semigroup UnbalancedTx where
    tx1 <> tx2 = UnbalancedTx {
        _inputs = _inputs tx1 <> _inputs tx2,
        _outputs = _outputs tx1 <> _outputs tx2,
        _forge = _forge tx1 <> _forge tx2,
        _forgeScripts = _forgeScripts tx1 <> _forgeScripts tx2,
        _requiredSignatories = _requiredSignatories tx1 <> _requiredSignatories tx2,
        _dataValues = _dataValues tx1 <> _dataValues tx2,
        _validityRange = _validityRange tx1 /\ _validityRange tx2,
        _valueMoved = _valueMoved tx1 <> _valueMoved tx2
        }

instance Monoid UnbalancedTx where
    mempty = UnbalancedTx mempty mempty mempty mempty mempty mempty top mempty

instance Pretty UnbalancedTx where
    pretty UnbalancedTx{_inputs, _outputs, _forge, _requiredSignatories, _dataValues, _validityRange, _valueMoved} =
        let renderOutput Tx.TxOut{Tx.txOutType, Tx.txOutValue} =
                hang 2 $ vsep ["-" <+> pretty txOutValue <+> "locked by", pretty txOutType]
            renderInput Tx.TxIn{Tx.txInRef,Tx.txInType} =
                let rest =
                        case txInType of
                            Tx.ConsumeScriptAddress _ redeemer _ ->
                                [pretty redeemer]
                            Tx.ConsumePublicKeyAddress -> mempty
                in hang 2 $ vsep $ "-" <+> pretty txInRef : rest
            lines' =
                [ hang 2 (vsep ("inputs:" : fmap renderInput (Set.toList _inputs)))
                , hang 2 (vsep ("outputs:" : fmap renderOutput _outputs))
                , "forge:" <+> pretty _forge
                , hang 2 (vsep ("required signatories:": fmap pretty _requiredSignatories))
                , hang 2 (vsep ("data values:" : fmap pretty _dataValues))
                , "validity range:" <+> viaShow _validityRange
                , "value moved:" <+> pretty _valueMoved
                ]
        in braces $ nest 2 $ vsep lines'

valueMoved :: UnbalancedTx -> Value
valueMoved = _valueMoved

requiredSignatories :: UnbalancedTx -> [PubKeyHash]
requiredSignatories = _requiredSignatories

validityRange :: UnbalancedTx -> SlotRange
validityRange = _validityRange

-- | Does the transaction modify the UTXO set?
modifiesUtxoSet :: UnbalancedTx -> Bool
modifiesUtxoSet UnbalancedTx{_inputs, _outputs} =
    not (null _inputs && null _outputs)

-- | Is there a valid transaction that satisfies the constraint?
hasValidTx :: UnbalancedTx -> Bool
hasValidTx UnbalancedTx{_validityRange} =
    not (I.isEmpty _validityRange)

-- | @mustBeValidIn r@ requires the transaction's slot range to be contained
--   in @r@.
mustBeValidIn :: SlotRange -> UnbalancedTx
mustBeValidIn range = mempty { _validityRange = range }

-- | Require the transaction to be signed by the public key.
mustBeSignedBy :: PubKeyHash -> UnbalancedTx
mustBeSignedBy pk = mempty { _requiredSignatories = [pk] }

-- | Require the transaction to spend the input
mustSpendInput :: L.TxIn -> UnbalancedTx
mustSpendInput i = mempty { _inputs = Set.singleton i }

-- | Require the transaction to produce the ouptut
mustProduceOutput :: L.TxOut -> UnbalancedTx
mustProduceOutput o = mempty { _outputs = [o] }

mustIncludeDataValue :: DataValue -> UnbalancedTx
mustIncludeDataValue dv = mempty { _dataValues = [dv] }

-- TODO: this is a bit of a hack, I'm not sure quite what the best way to avoid this is
-- (used in the typed contract stuff only)
fromLedgerTx :: L.Tx -> UnbalancedTx
fromLedgerTx tx = UnbalancedTx
            { _inputs = L.txInputs tx
            , _outputs = L.txOutputs tx
            , _forge = L.txForge tx
            , _requiredSignatories = fmap L.pubKeyHash $ Map.keys $ L.txSignatures tx
            , _dataValues = toList $ L.txData tx
            , _validityRange = L.txValidRange tx
            , _forgeScripts = L.txForgeScripts tx
            , _valueMoved = mempty
            }

-- | The ledger transaction of the 'UnbalancedTx'. Note that the result
--   does not have any signatures, and is potentially unbalanced (ie. invalid).
--   To produce a balanced 'Tx', use 'Language.Plutus.Contract.Wallet.balanceTx'.
toLedgerTx :: UnbalancedTx -> L.Tx
toLedgerTx utx =
    let tx = L.Tx
            { L.txInputs = _inputs utx
            , L.txOutputs = _outputs utx
            , L.txForge = _forge utx
            , L.txFee = mempty
            , L.txValidRange = _validityRange utx
            , L.txForgeScripts = _forgeScripts utx
            , L.txSignatures = Map.empty
            , L.txData = Map.fromList $ fmap (\ds -> (L.dataValueHash ds, ds)) (_dataValues utx)
            }
     in tx { L.txFee = minFee tx }

-- | Make an unbalanced transaction that does not forge any value. Note that duplicate inputs
--   will be ignored.
--   Note: this doesn't populate the data scripts, so is not exported. Prefer using 'payToScript' etc.
unbalancedTx :: [L.TxIn] -> [L.TxOut] -> UnbalancedTx
unbalancedTx ins outs = UnbalancedTx (Set.fromList ins) outs mempty mempty mempty mempty I.always mempty

-- | Create an `UnbalancedTx` that pays money to a script address.
payToScript :: Value -> Address -> DataValue -> UnbalancedTx
payToScript v a ds = (unbalancedTx mempty [outp]) { _dataValues = [ds] } where
    outp = Tx.scriptTxOut' v a ds

-- | Create an 'UnbalancedTx' that pays money to a public-key address
payToPubKey :: Value -> PubKey -> UnbalancedTx
payToPubKey v pk = unbalancedTx mempty [outp] where
    outp = Tx.pubKeyTxOut v pk

-- | Create an 'UnbalancedTx' that pays money to a public-key address
payToPubKeyHash :: Value -> PubKeyHash -> UnbalancedTx
payToPubKeyHash v pk = unbalancedTx mempty [outp] where
    outp = Tx.pubKeyHashTxOut v pk

-- | Create an `UnbalancedTx` that collects script outputs from the
--   address of the given validator script, using the same redeemer script
--   for all outputs. See 'Wallet.API.collectFromScript'.
collectFromScript
    :: AddressMap
    -> Validator
    -> RedeemerValue
    -> UnbalancedTx
collectFromScript = collectFromScriptFilter (\_ -> const True)

-- | See 'Wallet.API.collectFromScriptFilter'.
collectFromScriptFilter
    :: (TxOutRef -> TxOutTx -> Bool)
    -> AddressMap
    -> Validator
    -> RedeemerValue
    -> UnbalancedTx
collectFromScriptFilter flt am vls red =
    let inp = WAPI.getScriptInputsFilter flt am vls red
    in unbalancedTx (fmap fst inp) mempty

-- This just sets the '_forge' field, but it's exported for convenient
-- use with '<>'.
-- | An 'UnbalancedTx' that forges the specified value, using the given monetary policies as authorization.
forgeValue :: Value -> Set.Set L.MonetaryPolicy -> UnbalancedTx
forgeValue vl fs = mempty { _forge = vl, _forgeScripts = fs }

-- | An 'UnbalancedTx' that moves the specified value
moveValue :: Value -> UnbalancedTx
moveValue vl = mempty { _valueMoved = vl }

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
