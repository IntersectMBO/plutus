{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StrictData         #-}

module Cardano.Wallet.Types where

import           Data.Aeson             (FromJSON, ToJSON)
import           Data.Text              (Text)
import           GHC.Generics           (Generic)
import           Servant.Client         (BaseUrl)
import           Wallet.Emulator.Wallet (Wallet)

type WalletId = Integer

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
