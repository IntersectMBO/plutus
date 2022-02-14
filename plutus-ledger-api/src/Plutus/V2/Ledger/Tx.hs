{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Plutus.V2.Ledger.Tx(
    -- * Transactions
    TxId (..),
    ScriptTag (..),
    RedeemerPtr (..),
    Redeemers,
    -- * Transaction outputs
    TxOut(..),
    TxOutRef(..),
    OutputDatum (..),
    isPubKeyOut,
    isPayToScriptOut,
    outAddress,
    outValue,
    txOutPubKey,
    outDatum,
    pubKeyHashTxOut,
    -- * Transaction inputs
    TxInType(..),
    TxIn(..),
    inRef,
    inType,
    inScripts,
    pubKeyTxIn,
    scriptTxIn,
    pubKeyTxIns,
    scriptTxIns,
    ) where

import Control.DeepSeq (NFData)
import Control.Lens
import Data.Maybe (isJust)
import GHC.Generics (Generic)
import Prettyprinter

import PlutusTx qualified
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx

import Plutus.V1.Ledger.Address
import Plutus.V1.Ledger.Crypto
import Plutus.V1.Ledger.Scripts
import Plutus.V1.Ledger.Tx hiding (TxOut (..), isPayToScriptOut, isPubKeyOut, outAddress, outValue, pubKeyHashTxOut,
                            txOutDatum, txOutPubKey)
import Plutus.V1.Ledger.Value

-- | The datum attached to an output: either nothing; a datum hash; or the datum itself (an "inline datum").
data OutputDatum = NoOutputDatum | OutputDatumHash DatumHash | OutputDatum Datum
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance PlutusTx.Eq OutputDatum where
    {-# INLINABLE (==) #-}
    NoOutputDatum == NoOutputDatum                = True
    (OutputDatumHash dh) == (OutputDatumHash dh') = dh PlutusTx.== dh'
    (OutputDatum d) == (OutputDatum d')           = d PlutusTx.== d'
    _ == _                                        = False

instance Pretty OutputDatum where
    pretty NoOutputDatum        = "no datum"
    pretty (OutputDatumHash dh) = "datum hash: " <+> pretty dh
    pretty (OutputDatum d)      = "inline datum : " <+> pretty d

-- | A transaction output, consisting of a target address, a value, and optionally a datum hash.
data TxOut = TxOut {
    txOutAddress :: Address,
    txOutValue   :: Value,
    txOutDatum   :: OutputDatum
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Pretty TxOut where
    pretty TxOut{txOutAddress, txOutValue, txOutDatum} =
                hang 2 $ vsep ["-" <+> pretty txOutValue <+> "addressed to", pretty txOutAddress, "with datum", pretty txOutDatum]

instance PlutusTx.Eq TxOut where
    {-# INLINABLE (==) #-}
    (TxOut txOutAddress txOutValue txOutDatum) == (TxOut txOutAddress' txOutValue' txOutDatum') =
        txOutAddress PlutusTx.== txOutAddress'
        PlutusTx.&& txOutValue PlutusTx.== txOutValue'
        PlutusTx.&& txOutDatum PlutusTx.== txOutDatum'

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey TxOut{txOutAddress} = toPubKeyHash txOutAddress

-- | The validator hash attached to a 'TxOut', if there is one.
txOutValidatorHash :: TxOut -> Maybe ValidatorHash
txOutValidatorHash TxOut{txOutAddress} = toValidatorHash txOutAddress

-- | The address of a transaction output.
outAddress :: Lens' TxOut Address
outAddress = lens txOutAddress s where
    s tx a = tx { txOutAddress = a }

-- | The datum attached to a 'TxOut'.
outDatum :: Lens' TxOut OutputDatum
outDatum = lens txOutDatum s where
    s tx v = tx { txOutDatum = v }

-- | The value of a transaction output.
-- | TODO: Compute address again
outValue :: Lens' TxOut Value
outValue = lens txOutValue s where
    s tx v = tx { txOutValue = v }

-- | Whether the output is a pay-to-pubkey output.
isPubKeyOut :: TxOut -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Whether the output is a pay-to-script output.
isPayToScriptOut :: TxOut -> Bool
isPayToScriptOut = isJust . txOutValidatorHash

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v NoOutputDatum

PlutusTx.makeIsDataIndexed ''OutputDatum [('NoOutputDatum,0), ('OutputDatumHash,1), ('OutputDatum,2)]
PlutusTx.makeLift ''OutputDatum
PlutusTx.makeIsDataIndexed ''TxOut [('TxOut,0)]
PlutusTx.makeLift ''TxOut
