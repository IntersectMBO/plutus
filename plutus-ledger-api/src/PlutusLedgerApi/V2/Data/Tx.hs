{-# LANGUAGE CPP               #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
#if !MIN_VERSION_base(4,15,0)
{-# OPTIONS_GHC -Wno-name-shadowing #-}
#endif
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusLedgerApi.V2.Data.Tx (
  -- * Transactions
  TxId (..),
  ScriptTag (..),
  RedeemerPtr (..),
  Redeemers,

  -- * Transaction outputs
  TxOut,
  pattern TxOut,
  txOutAddress,
  txOutValue,
  txOutDatum,
  txOutReferenceScript,
  TxOutRef,
  pattern TxOutRef,
  txOutRefId,
  txOutRefIdx,
  OutputDatum,
  pattern NoOutputDatum,
  pattern OutputDatumHash,
  pattern OutputDatum,
  isPubKeyOut,
  isPayToScriptOut,
  outAddress,
  outValue,
  txOutPubKey,
  outDatum,
  outReferenceScript,
  pubKeyHashTxOut,
) where

import Control.DeepSeq (NFData)
import Control.Lens
import Data.Maybe (isJust)
import GHC.Generics (Generic)
import Prettyprinter

import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Bool qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx

import PlutusLedgerApi.V1.Crypto
import PlutusLedgerApi.V1.Data.Address
import PlutusLedgerApi.V1.Data.Tx hiding (TxOut, isPayToScriptOut, isPubKeyOut, outAddress,
                                   outValue, pattern TxOut, pubKeyHashTxOut, txOutAddress,
                                   txOutDatum, txOutDatumHash, txOutPubKey, txOutValue)
import PlutusLedgerApi.V1.Data.Value
import PlutusLedgerApi.V1.Scripts

{-| The datum attached to an output: either nothing; a datum hash;
or the datum itself (an "inline datum").
-}
PlutusTx.asData
  [d|
    data OutputDatum = NoOutputDatum | OutputDatumHash DatumHash | OutputDatum Datum
      deriving stock (Show, Eq, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving anyclass (NFData)
    |]

instance PlutusTx.Eq OutputDatum where
  {-# INLINEABLE (==) #-}
  NoOutputDatum == NoOutputDatum                = True
  (OutputDatumHash dh) == (OutputDatumHash dh') = dh PlutusTx.== dh'
  (OutputDatum d) == (OutputDatum d')           = d PlutusTx.== d'
  _ == _                                        = False

instance Pretty OutputDatum where
  pretty NoOutputDatum        = "no datum"
  pretty (OutputDatumHash dh) = "datum hash: " <+> pretty dh
  pretty (OutputDatum d)      = "inline datum : " <+> pretty d

{-| A transaction output, consisting of a target address, a value,
optionally a datum/datum hash, and optionally a reference script.
-}
PlutusTx.asData
  [d|
    data TxOut = TxOut
      { txOutAddress :: Address
      , txOutValue :: Value
      , txOutDatum :: OutputDatum
      , txOutReferenceScript :: Maybe ScriptHash
      }
      deriving stock (Show, Eq, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

instance Pretty TxOut where
  pretty TxOut{txOutAddress, txOutValue, txOutDatum, txOutReferenceScript} =
    hang 2 $
      vsep
        [ "-" <+> pretty txOutValue <+> "addressed to"
        , pretty txOutAddress
        , "with datum"
        , pretty txOutDatum
        , "with referenceScript"
        , pretty txOutReferenceScript
        ]

instance PlutusTx.Eq TxOut where
  {-# INLINEABLE (==) #-}
  (TxOut txOutAddress1 txOutValue1 txOutDatum1 txOutRefScript1)
    == (TxOut txOutAddress2 txOutValue2 txOutDatum2 txOutRefScript2) =
      txOutAddress1
        PlutusTx.== txOutAddress2
        PlutusTx.&& txOutValue1
        PlutusTx.== txOutValue2
        PlutusTx.&& txOutDatum1
        PlutusTx.== txOutDatum2
        PlutusTx.&& txOutRefScript1
        PlutusTx.== txOutRefScript2

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey = toPubKeyHash . txOutAddress

-- | The validator hash attached to a 'TxOut', if there is one.
txOutScriptHash :: TxOut -> Maybe ScriptHash
txOutScriptHash = toScriptHash . txOutAddress

-- | The address of a transaction output.
outAddress :: Lens' TxOut Address
outAddress = lens txOutAddress s
 where
  s tx a = tx{txOutAddress = a}

-- | The datum attached to a 'TxOut'.
outDatum :: Lens' TxOut OutputDatum
outDatum = lens txOutDatum s
 where
  s tx v = tx{txOutDatum = v}

{-| The value of a transaction output.
| TODO: Compute address again
-}
outValue :: Lens' TxOut Value
outValue = lens txOutValue s
 where
  s tx v = tx{txOutValue = v}

-- | The reference script attached to a 'TxOut'.
outReferenceScript :: Lens' TxOut (Maybe ScriptHash)
outReferenceScript = lens txOutReferenceScript s
 where
  s tx v = tx{txOutReferenceScript = v}

-- | Whether the output is a pay-to-pubkey output.
isPubKeyOut :: TxOut -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Whether the output is a pay-to-script output.
isPayToScriptOut :: TxOut -> Bool
isPayToScriptOut = isJust . txOutScriptHash

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v NoOutputDatum Nothing

PlutusTx.makeLift ''OutputDatum
PlutusTx.makeLift ''TxOut
