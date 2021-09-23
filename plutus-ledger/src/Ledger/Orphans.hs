{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Ledger.Orphans where

import qualified Cardano.Crypto.Wallet          as Crypto
import           Control.Lens                   ((&), (.~), (?~))
import           Control.Monad.Freer.Extras.Log (LogLevel, LogMessage)
import qualified Data.Aeson                     as JSON
import qualified Data.Aeson.Extras              as JSON
import           Data.Bifunctor                 (bimap)
import qualified Data.OpenApi                   as OpenApi
import qualified Data.Text                      as Text
import           Data.Typeable
import           GHC.Exts                       (IsList (..))
import           Plutus.V1.Ledger.Api
import           Plutus.V1.Ledger.Bytes         (bytes)
import           Plutus.V1.Ledger.Crypto        (PrivateKey (PrivateKey, getPrivateKey), PubKey (..), Signature (..))
import           Plutus.V1.Ledger.Slot          (Slot (..))
import           Plutus.V1.Ledger.Tx
import           Plutus.V1.Ledger.Value
import           PlutusCore
import           Prelude                        as Haskell
import           Web.HttpApiData                (FromHttpApiData (..), ToHttpApiData (..))


instance ToHttpApiData PrivateKey where
    toUrlPiece = toUrlPiece . getPrivateKey

instance FromHttpApiData PrivateKey where
    parseUrlPiece a = PrivateKey <$> parseUrlPiece a

instance ToHttpApiData LedgerBytes where
    toUrlPiece = JSON.encodeByteString . bytes
instance FromHttpApiData LedgerBytes where
    parseUrlPiece = bimap Text.pack fromBytes . JSON.tryDecode

-- | OpenApi instances for swagger support

instance OpenApi.ToSchema Crypto.XPub where
    declareNamedSchema _ = pure $ OpenApi.NamedSchema (Just "PubKey") mempty
instance OpenApi.ToSchema Crypto.XPrv where
    declareNamedSchema _ = pure $ OpenApi.NamedSchema (Just "PrvKey") mempty
deriving instance OpenApi.ToSchema (LogMessage JSON.Value)
deriving instance OpenApi.ToSchema LogLevel
instance OpenApi.ToSchema JSON.Value where
    declareNamedSchema _ = pure $ OpenApi.NamedSchema (Just "JSON") mempty
instance OpenApi.ToSchema Data where
  declareNamedSchema _ = do
    integerSchema <- OpenApi.declareSchemaRef (Proxy :: Proxy Integer)
    constrArgsSchema <- OpenApi.declareSchemaRef (Proxy :: Proxy (Integer, [Data]))
    mapArgsSchema <- OpenApi.declareSchemaRef (Proxy :: Proxy [(Data, Data)])
    listArgsSchema <- OpenApi.declareSchemaRef (Proxy :: Proxy [Data])
    bytestringSchema <- OpenApi.declareSchemaRef (Proxy :: Proxy String)
    return $ OpenApi.NamedSchema (Just "Data") $ mempty
      & OpenApi.type_ ?~ OpenApi.OpenApiObject
      & OpenApi.properties .~
          fromList
          [ ("Constr", constrArgsSchema)
          , ("Map", mapArgsSchema)
          , ("List", listArgsSchema)
          , ("I", integerSchema)
          , ("B", bytestringSchema)
          ]
deriving instance OpenApi.ToSchema ann => OpenApi.ToSchema (Kind ann)
deriving instance OpenApi.ToSchema Tx
deriving instance OpenApi.ToSchema ScriptTag
deriving instance OpenApi.ToSchema RedeemerPtr
deriving instance OpenApi.ToSchema TxOutRef
deriving instance OpenApi.ToSchema TxInType
deriving instance OpenApi.ToSchema TxIn
deriving instance OpenApi.ToSchema TxOut
deriving newtype instance OpenApi.ToSchema Validator
deriving newtype instance OpenApi.ToSchema TxId
deriving newtype instance OpenApi.ToSchema Slot
deriving instance OpenApi.ToSchema a => OpenApi.ToSchema (Interval a)
deriving instance OpenApi.ToSchema a => OpenApi.ToSchema (LowerBound a)
deriving instance OpenApi.ToSchema a => OpenApi.ToSchema (UpperBound a)
deriving newtype instance OpenApi.ToSchema Redeemer
deriving newtype instance OpenApi.ToSchema RedeemerHash
deriving newtype instance OpenApi.ToSchema Datum
deriving newtype instance OpenApi.ToSchema Value
deriving instance OpenApi.ToSchema Address
deriving newtype instance OpenApi.ToSchema MintingPolicy
deriving newtype instance OpenApi.ToSchema MintingPolicyHash
deriving newtype instance OpenApi.ToSchema DatumHash
deriving newtype instance OpenApi.ToSchema CurrencySymbol
deriving instance OpenApi.ToSchema Credential
deriving newtype instance OpenApi.ToSchema PubKey
deriving newtype instance OpenApi.ToSchema TokenName
deriving instance OpenApi.ToSchema StakingCredential
deriving newtype instance OpenApi.ToSchema StakeValidatorHash
deriving newtype instance OpenApi.ToSchema PubKeyHash
deriving newtype instance OpenApi.ToSchema LedgerBytes
deriving newtype instance OpenApi.ToSchema ValidatorHash
deriving newtype instance OpenApi.ToSchema Signature
deriving newtype instance OpenApi.ToSchema POSIXTime
deriving newtype instance OpenApi.ToSchema BuiltinData
deriving newtype instance OpenApi.ToSchema AssetClass
deriving instance OpenApi.ToSchema a => OpenApi.ToSchema (Extended a)
deriving instance
    ( OpenApi.ToSchema tyname
    , OpenApi.ToSchema name
    , OpenApi.ToSchema (uni ann)
    , OpenApi.ToSchema fun
    , OpenApi.ToSchema ann
    , OpenApi.ToSchema (Type tyname uni ann)
    , OpenApi.ToSchema (Some (ValueOf uni))
    , Typeable uni
    ) => OpenApi.ToSchema (Term tyname name uni fun ann)
deriving instance OpenApi.ToSchema ann => OpenApi.ToSchema (Version ann)
instance OpenApi.ToSchema Script where
    declareNamedSchema _ =
        Haskell.pure $ OpenApi.NamedSchema (Just "Script") (OpenApi.toSchema (Proxy :: Proxy String))
