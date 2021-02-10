{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Ledger.Orphans where

import qualified Data.Aeson.Extras       as JSON
import           Data.Bifunctor          (bimap)
import qualified Data.Text               as Text
import           Plutus.V1.Ledger.Bytes
import           Plutus.V1.Ledger.Crypto
import           Web.HttpApiData         (FromHttpApiData (..), ToHttpApiData (..))

instance ToHttpApiData PrivateKey where
    toUrlPiece = toUrlPiece . getPrivateKey

instance FromHttpApiData PrivateKey where
    parseUrlPiece a = PrivateKey <$> parseUrlPiece a

instance ToHttpApiData LedgerBytes where
    toUrlPiece = JSON.encodeByteString . bytes
instance FromHttpApiData LedgerBytes where
    parseUrlPiece = bimap Text.pack fromBytes . JSON.tryDecode
