{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TemplateHaskell            #-}
module Wallet.Rollup.Types where

import           Control.Lens (makeLenses)
import           Data.Aeson   (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Map     (Map)
import           GHC.Generics
import           Ledger

data SequenceId =
    SequenceId
        { slotIndex :: Int
        , txIndex   :: Int
        }
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

data DereferencedInput =
    DereferencedInput
        { originalInput :: TxIn
        , refersTo      :: TxOut
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

data BeneficialOwner
    = OwnedByPubKey PubKey
    | OwnedByScript Address
    deriving (Eq, Show, Ord, Generic)
    deriving anyclass (FromJSON, ToJSON, FromJSONKey, ToJSONKey)

toBeneficialOwner :: TxOut -> BeneficialOwner
toBeneficialOwner TxOut {txOutType, txOutAddress} =
    case txOutType of
        PayToPubKey pubKey -> OwnedByPubKey pubKey
        PayToScript _      -> OwnedByScript txOutAddress

data AnnotatedTx =
    AnnotatedTx
        { sequenceId         :: SequenceId
        , txId               :: TxId
        , tx                 :: Tx
        , dereferencedInputs :: [DereferencedInput]
        , balances           :: Map BeneficialOwner Value
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

makeLenses 'SequenceId

makeLenses 'AnnotatedTx
