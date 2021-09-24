{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TemplateHaskell            #-}

module Wallet.Rollup.Types where

import           Control.Lens              (makeLenses, makeLensesFor)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Map                  (Map)
import qualified Data.OpenApi.Schema       as OpenApi
import           Data.Text.Prettyprint.Doc (Pretty, pretty, viaShow)
import           GHC.Generics
import           Ledger
import           Ledger.Credential         (Credential (..))

data TxKey =
    TxKey
        { _txKeyTxId        :: TxId
        , _txKeyTxOutRefIdx :: Integer
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (FromJSON, ToJSON, OpenApi.ToSchema)

instance Pretty TxKey where
    pretty = viaShow

data SequenceId =
    SequenceId
        { slotIndex :: Int
        , txIndex   :: Int
        }
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, OpenApi.ToSchema)

makeLensesFor
     [ ("slotIndex", "slotIndexL")
     , ("txIndex", "txIndexL")
     ]
    ''SequenceId

data DereferencedInput
    = DereferencedInput
          { originalInput :: TxIn
          , refersTo      :: TxOut
          }
    | InputNotFound TxKey
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, OpenApi.ToSchema)

isFound :: DereferencedInput -> Bool
isFound DereferencedInput {} = True
isFound (InputNotFound _)    = False

data BeneficialOwner
    = OwnedByPubKey PubKeyHash
    | OwnedByScript ValidatorHash
    deriving (Eq, Show, Ord, Generic)
    deriving anyclass (FromJSON, ToJSON, OpenApi.ToSchema, FromJSONKey, ToJSONKey)

toBeneficialOwner :: TxOut -> BeneficialOwner
toBeneficialOwner TxOut {txOutAddress=Address{addressCredential}} =
    case addressCredential of
        PubKeyCredential pkh -> OwnedByPubKey pkh
        ScriptCredential vh  -> OwnedByScript vh

data AnnotatedTx =
    AnnotatedTx
        { sequenceId         :: SequenceId
        , txId               :: TxId
        , tx                 :: Tx
        , dereferencedInputs :: [DereferencedInput]
        , balances           :: Map BeneficialOwner Value
        , valid              :: Bool
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, OpenApi.ToSchema)

makeLenses 'AnnotatedTx

data Rollup =
    Rollup
        { _previousOutputs :: Map TxKey TxOut
        , _rollingBalances :: Map BeneficialOwner Value
        }
    deriving (Show, Eq, Generic)

makeLenses 'Rollup

data RollupState =
    RollupState
        { _currentSequenceId     :: SequenceId
        , _rollup                :: Rollup
        , _annotatedTransactions :: [AnnotatedTx] -- reverse order
        }

makeLenses ''RollupState
