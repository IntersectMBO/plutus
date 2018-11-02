{-# LANGUAGE AutoDeriveTypeable         #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

module PSGenerator
  ( generate
  ) where

import           Control.Applicative                ((<|>))
import           Control.Lens                       (set, (&))
import           Data.Aeson                         (FromJSON, ToJSON)
import           Data.Monoid                        ()
import           Data.Proxy                         (Proxy (Proxy))
import qualified Data.Set                           as Set ()
import           Data.Text                          (Text)
import qualified Data.Text                          as T ()
import qualified Data.Text.Encoding                 as T ()
import qualified Data.Text.IO                       as T ()
import           GHC.Generics                       (Generic)
import           Language.PureScript.Bridge         (BridgePart, Language (Haskell), SumType, buildBridge, mkSumType,
                                                     stringBridge, writePSTypes)
import           Language.PureScript.Bridge.PSTypes ()
import           Playground.API                     (API, Evaluation, Fn, SourceCode)
import           Servant.API                        ((:>), Capture, Get, JSON, PlainText, Post, ReqBody)
import           Servant.PureScript                 (HasBridge, Settings, apiModuleName, defaultBridge, defaultSettings,
                                                     languageBridge, writeAPIModuleWithSettings, _generateSubscriberAPI)
import           Wallet.UTXO.Types                  (Blockchain)

myBridge :: BridgePart
myBridge = defaultBridge

newtype WalletId =
  WalletId String
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)

data Wallet = Wallet
  { id      :: WalletId
  , balance :: Double
  }
  deriving stock (Generic)

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
  languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes = [mkSumType (Proxy @WalletId), mkSumType (Proxy @Wallet)]

mySettings :: Settings
mySettings =
  (defaultSettings & set apiModuleName "Playground.Server")
    {_generateSubscriberAPI = False}

generate :: FilePath -> IO ()
generate outputDir = do
  writeAPIModuleWithSettings
    mySettings
    outputDir
    myBridgeProxy
    (Proxy :: Proxy ("version" :> Get '[PlainText, JSON] Text))
  writePSTypes outputDir (buildBridge myBridge) myTypes
