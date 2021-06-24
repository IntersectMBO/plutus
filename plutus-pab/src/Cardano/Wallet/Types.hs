{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

module Cardano.Wallet.Types (
     -- * effect type for the mock wallet
      WalletEffects
    , Wallets
    , MultiWalletEffect (..)
    , createWallet
    , multiWallet
     -- * wallet configuration
    , WalletConfig (..)

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
import           Data.Map.Strict                    (Map)
import           Data.Text                          (Text)
import           Data.Text.Prettyprint.Doc          (Pretty (..), (<+>))
import           GHC.Generics                       (Generic)
import           Ledger                             (PubKey, PubKeyHash)
import           Plutus.PAB.Arbitrary               ()
import           Servant                            (ServerError (..))
import           Servant.Client                     (BaseUrl, ClientError)
import           Servant.Client.Internal.HttpClient (ClientEnv)
import           Wallet.Effects                     (ChainIndexEffect, NodeClientEffect, WalletEffect)
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
                        , ChainIndexEffect
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

data WalletConfig =
    WalletConfig
        { baseUrl :: WalletUrl
        , wallet  :: Wallet
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

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
