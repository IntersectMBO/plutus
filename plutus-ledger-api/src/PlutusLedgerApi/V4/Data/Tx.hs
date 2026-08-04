{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
-- needed for asData pattern synonyms
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Data.Tx
  ( -- * Transactions
    TxId (..)

    -- * Transaction outputs
  , TxOutRef
  , pattern TxOutRef
  , matchTxOutRef
  , txOutRefId
  , txOutRefIdx
  , OutputDatum
  , matchOutputDatum
  , pattern NoOutputDatum
  , pattern OutputDatumHash
  , pattern OutputDatum
  , TxOut
  , pattern TxOut
  , matchTxOut
  , txOutAddress
  , txOutValue
  , txOutDatum
  , txOutReferenceScript
  , txOutPubKey
  , txOutScriptHash
  , isPubKeyOut
  , isPayToScriptOut
  , pubKeyHashTxOut
  ) where

import Data.Maybe (isJust)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Data.Value (Value)
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import PlutusLedgerApi.V2.Data.Tx
  ( OutputDatum
  , matchOutputDatum
  , pattern NoOutputDatum
  , pattern OutputDatum
  , pattern OutputDatumHash
  )
import PlutusLedgerApi.V3.Data.Tx
  ( TxId (..)
  , TxOutRef
  , matchTxOutRef
  , txOutRefId
  , txOutRefIdx
  , pattern TxOutRef
  )
import PlutusLedgerApi.V4.Data.Address
  ( Address
  , pubKeyHashAddress
  , toPubKeyHash
  , toScriptHash
  )
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Eq qualified as PlutusTx
import Prettyprinter (Pretty (pretty), hang, vsep, (<+>))

-- | Transaction output for Plutus V4.
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

PlutusTx.deriveEq ''TxOut

instance Pretty TxOut where
  pretty TxOut {txOutAddress, txOutValue, txOutDatum, txOutReferenceScript} =
    hang 2 $
      vsep
        [ "-" <+> pretty txOutValue <+> "addressed to"
        , pretty txOutAddress
        , "with datum"
        , pretty txOutDatum
        , "with referenceScript"
        , pretty txOutReferenceScript
        ]

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey = toPubKeyHash . txOutAddress

-- | The validator hash attached to a 'TxOut', if there is one.
txOutScriptHash :: TxOut -> Maybe ScriptHash
txOutScriptHash = toScriptHash . txOutAddress

-- | Whether the output is a pay-to-pubkey output.
isPubKeyOut :: TxOut -> Bool
isPubKeyOut = isJust . txOutPubKey

-- | Whether the output is a pay-to-script output.
isPayToScriptOut :: TxOut -> Bool
isPayToScriptOut = isJust . txOutScriptHash

-- | Create a transaction output locked by a public key.
pubKeyHashTxOut :: Value -> PubKeyHash -> TxOut
pubKeyHashTxOut v pkh = TxOut (pubKeyHashAddress pkh) v NoOutputDatum Nothing

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(PlutusTx.makeLift ''TxOut)
