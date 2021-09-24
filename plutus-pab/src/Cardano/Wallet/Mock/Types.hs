{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.Wallet.Mock.Types (
     -- * effect type for the mock wallet
      WalletEffects
    , Wallets
    , MultiWalletEffect (..)
    , createWallet
    , multiWallet
     -- * wallet configuration
    , WalletConfig (..)
    , defaultWalletConfig

     -- * wallet log messages
    , WalletMsg (..)

     -- * newtypes for convenience
    , Port (..)
    , NodeClient (..)
    , ChainClient (..)
    , WalletUrl (..)
    , ChainIndexUrl
    -- * Wallet info
    , WalletInfo(..)
    ) where

import           Cardano.BM.Data.Tracer             (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras      (Tagged (..), mkObjectStr)
import           Cardano.ChainIndex.Types           (ChainIndexUrl)
import           Control.Monad.Freer                (Eff)
import           Control.Monad.Freer.Error          (Error)
import           Control.Monad.Freer.Extras.Log     (LogMsg)
import           Control.Monad.Freer.State          (State)
import           Control.Monad.Freer.TH             (makeEffect)
import           Data.Aeson                         (FromJSON, ToJSON)
import           Data.Default                       (Default, def)
import           Data.Map.Strict                    (Map)
import           Data.Text                          (Text)
import           Data.Text.Prettyprint.Doc          (Pretty (..), (<+>))
import           GHC.Generics                       (Generic)
import           Ledger                             (PubKey, PubKeyHash)
import           Plutus.ChainIndex                  (ChainIndexQueryEffect)
import           Plutus.PAB.Arbitrary               ()
import           Servant                            (ServerError (..))
import           Servant.Client                     (BaseUrl (..), ClientError, Scheme (..))
import           Servant.Client.Internal.HttpClient (ClientEnv)
import           Wallet.Effects                     (NodeClientEffect, WalletEffect)
import           Wallet.Emulator.Error              (WalletAPIError)
import           Wallet.Emulator.LogMessages        (TxBalanceMsg)
import           Wallet.Emulator.Wallet             (Wallet, WalletState)

-- | Information about an emulated wallet.
data WalletInfo =
    WalletInfo
        { wiWallet     :: Wallet
        , wiPubKey     :: PubKey
        , wiPubKeyHash :: PubKeyHash
        }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

type Wallets = Map Wallet WalletState

data MultiWalletEffect r where
    CreateWallet :: MultiWalletEffect WalletInfo
    MultiWallet :: Wallet -> Eff '[WalletEffect] a -> MultiWalletEffect a
makeEffect ''MultiWalletEffect

type WalletEffects m = '[ MultiWalletEffect
                        , NodeClientEffect
                        , ChainIndexQueryEffect
                        , State Wallets
                        , LogMsg Text
                        , Error WalletAPIError
                        , Error ClientError
                        , Error ServerError
                        , m]

newtype NodeClient = NodeClient ClientEnv

newtype ChainClient = ChainClient ClientEnv

newtype WalletUrl = WalletUrl BaseUrl
    deriving (Eq, Show, ToJSON, FromJSON) via BaseUrl

newtype Port = Port Int
    deriving (Show)
    deriving (Eq, Num, ToJSON, FromJSON, Pretty) via Int

newtype WalletConfig =
    WalletConfig
        { baseUrl :: WalletUrl
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

defaultWalletConfig :: WalletConfig
defaultWalletConfig =
  WalletConfig
    -- See Note [pab-ports] in "test/full/Plutus/PAB/CliSpec.hs".
    { baseUrl = WalletUrl $ BaseUrl Http "localhost" 9081 ""
    }

instance Default WalletConfig where
  def = defaultWalletConfig

data WalletMsg = StartingWallet Port
               | ChainClientMsg Text
               | Balancing TxBalanceMsg
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty WalletMsg where
    pretty = \case
        StartingWallet port -> "Starting wallet server on port " <+> pretty port
        ChainClientMsg m    -> "Chain Client: " <+> pretty m
        Balancing m         -> pretty m

instance ToObject WalletMsg where
    toObject _ = \case
        StartingWallet port -> mkObjectStr "Starting wallet server" (Tagged @"port" port)
        ChainClientMsg m    -> mkObjectStr "Chain Client: " (Tagged @"msg" m)
        Balancing m         -> mkObjectStr "Balancing" (Tagged @"msg" m)
