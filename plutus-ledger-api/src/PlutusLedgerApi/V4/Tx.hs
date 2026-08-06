{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Tx
  ( -- * Transactions
    TxId (..)

    -- * Transaction outputs
  , TxOutRef (..)
  , OutputDatum (..)
  , TxOut (..)
  , txOutPubKey
  , txOutScriptHash
  , isPubKeyOut
  , isPayToScriptOut
  , pubKeyHashTxOut
  ) where

import Data.Maybe (isJust)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Scripts (ScriptHash)
import PlutusLedgerApi.V1.Value (Value)
import PlutusLedgerApi.V2.Tx (OutputDatum (..))
import PlutusLedgerApi.V3.Tx (TxId (..), TxOutRef (..))
import PlutusLedgerApi.V4.Address
  ( Address
  , pubKeyHashAddress
  , toPubKeyHash
  , toScriptHash
  )
import PlutusTx qualified
import PlutusTx.Blueprint (HasBlueprintDefinition, definitionRef)
import PlutusTx.Eq qualified as PlutusTx
import Prettyprinter (Pretty (pretty), hang, vsep, (<+>))

-- | Transaction output for Plutus V4.
data TxOut = TxOut
  { txOutAddress :: Address
  , txOutValue :: Value
  , txOutDatum :: OutputDatum
  , txOutReferenceScript :: Maybe ScriptHash
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''TxOut

instance Pretty TxOut where
  pretty TxOut {txOutAddress, txOutValue, txOutDatum, txOutReferenceScript} =
    hang 2 $
      vsep
        [ "-"
            <+> pretty txOutValue
            <+> "addressed to"
        , pretty txOutAddress
        , "with datum"
        , pretty txOutDatum
        , "with referenceScript"
        , pretty txOutReferenceScript
        ]

-- | The public key attached to a 'TxOut', if there is one.
txOutPubKey :: TxOut -> Maybe PubKeyHash
txOutPubKey TxOut {txOutAddress} = toPubKeyHash txOutAddress

-- | The validator hash attached to a 'TxOut', if there is one.
txOutScriptHash :: TxOut -> Maybe ScriptHash
txOutScriptHash TxOut {txOutAddress} = toScriptHash txOutAddress

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

$(PlutusTx.makeIsDataSchemaIndexed ''TxOut [('TxOut, 0)])
$(PlutusTx.makeLift ''TxOut)
