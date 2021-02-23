{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Wallet.Types (
     -- * effect type for the mock wallet
      WalletEffects

     -- * wallet configuration
    , WalletConfig (..)

     -- * wallet log messages
    , WalletMsg (..)

     -- * newtypes for convenience
    , NodeUrl (..)
    , ChainIndexUrl (..)
    , Port (..)
    , NodeClient (..)
    , ChainClient (..)
    , WalletUrl (..)
    ) where

import           Control.Monad.Freer.Error          (Error)
import           Control.Monad.Freer.Extras.Log     (LogMsg)
import           Control.Monad.Freer.State          (State)
import           Data.Aeson                         (FromJSON, ToJSON)
import           Data.Text                          (Text)
import           Data.Text.Prettyprint.Doc          (Pretty (..), (<+>))
import           GHC.Generics                       (Generic)
import           Servant                            (ServerError (..))
import           Servant.Client                     (BaseUrl, ClientError)

import           Cardano.BM.Data.Tracer             (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras      (Tagged (..), mkObjectStr)
import           Plutus.PAB.Arbitrary               ()
import           Servant.Client.Internal.HttpClient (ClientEnv)
import           Wallet.Effects                     (ChainIndexEffect, NodeClientEffect, WalletEffect)
import           Wallet.Emulator.Error              (WalletAPIError)
import           Wallet.Emulator.Wallet             (Wallet, WalletState)

type WalletEffects m = '[ WalletEffect
                        , NodeClientEffect
                        , ChainIndexEffect
                        , State WalletState
                        , LogMsg Text
                        , Error WalletAPIError
                        , Error ClientError
                        , Error ServerError
                        , m]

newtype NodeClient = NodeClient ClientEnv

newtype ChainClient = ChainClient ClientEnv

newtype NodeUrl = NodeUrl BaseUrl
    deriving (Eq, Show) via BaseUrl

newtype WalletUrl = WalletUrl BaseUrl
    deriving (Eq, Show, ToJSON, FromJSON) via BaseUrl

newtype ChainIndexUrl = ChainIndexUrl BaseUrl
    deriving (Eq, Show) via BaseUrl

newtype Port = Port Int
    deriving (Show)
    deriving (Eq, Num, ToJSON, FromJSON, Pretty) via Int

data WalletConfig =
    WalletConfig
        { baseUrl :: WalletUrl
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
