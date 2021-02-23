{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.SigningProcess.Types
    ( SigningProcessEffects
    , SigningProcessMsg (..)
    , SigningProcessConfig (..)
    , WalletUrl
    ) where

import           Control.Monad.Freer.Error     (Error)
import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc     (Pretty (..), (<+>))
import           GHC.Generics                  (Generic)

import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (Tagged (..), mkObjectStr)
import           Cardano.Wallet.Types          (WalletUrl)
import           Control.Monad.Freer.State     (State)
import           Wallet                        (SigningProcessEffect)
import qualified Wallet.API                    as WAPI
import           Wallet.Emulator.Wallet        (SigningProcess, Wallet)

type SigningProcessEffects =
    '[ SigningProcessEffect, State SigningProcess, Error WAPI.WalletAPIError]


data SigningProcessConfig =
    SigningProcessConfig
        { spWallet  :: Wallet -- Wallet with whose private key transactions should be signed.
        , spBaseUrl :: WalletUrl
        } deriving stock (Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON)


newtype SigningProcessMsg =
    StartingSigningProcess Int -- ^ Starting up on the specified port
        deriving stock (Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty SigningProcessMsg where
    pretty = \case
        StartingSigningProcess port -> "Starting Signing Process on port " <+> pretty port

instance ToObject SigningProcessMsg where
    toObject _ = \case
        StartingSigningProcess p -> mkObjectStr "starting signing process" (Tagged @"port" p)
