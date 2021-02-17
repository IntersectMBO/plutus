{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.Wallet.Types where

import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (Tagged (..), mkObjectStr)
import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Text                     (Text)
import           Data.Text.Prettyprint.Doc     (Pretty (..), (<+>))
import           GHC.Generics                  (Generic)
import           Servant.Client                (BaseUrl)
import           Wallet.Emulator.Wallet        (Wallet)

type NodeUrl = BaseUrl
type ChainIndexUrl = BaseUrl
type WalletId = Integer
type Port     = Int

data Amount =
    Amount
        { quantity :: Integer
        , unit     :: Text
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data Coin =
    Coin
        { address :: Text
        , amount  :: Amount
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

newtype CoinSelectionRequest =
    CoinSelectionRequest
        { payments :: [Coin]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data CoinSelectionResponse =
    CoinSelectionResponse
        { inputs  :: [Coin]
        , outputs :: [Coin]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data Config =
    Config
        { baseUrl :: BaseUrl
        , wallet  :: Wallet
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

data WalletMsg = StartingWallet Port
                  | ChainClientMsg Text
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty WalletMsg where
    pretty = \case
        StartingWallet port -> "Starting wallet server on port " <+> pretty port
        ChainClientMsg m    -> "Chain Client: " <+> pretty m

instance ToObject WalletMsg where
    toObject _ = \case
        StartingWallet port -> mkObjectStr "Starting wallet server" (Tagged @"port" port)
        ChainClientMsg m    -> mkObjectStr "Chain Client: " (Tagged @"msg" m)
