{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PSGenerator
  ( generate,
  )
where

import           API                                        (HTTPAPI)
import           Control.Applicative                        ((<|>))
import           Control.Lens                               (set, (&))
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import qualified Data.Text.Encoding                         as T ()
import qualified Data.Text.IO                               as T ()
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), SumType, buildBridge,
                                                             typeName, writePSTypesWith, (^==))
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), defaultSwitch, genForeign)
import           Language.PureScript.Bridge.PSTypes         (psNumber, psString)
import qualified PSGenerator.Common
import           Servant.PureScript                         (HasBridge, Settings, _generateSubscriberAPI, apiModuleName,
                                                             defaultBridge, defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings)

doubleBridge :: BridgePart
doubleBridge = typeName ^== "Double" >> return psNumber

dayBridge :: BridgePart
dayBridge = typeName ^== "Day" >> return psString

myBridge :: BridgePart
myBridge =
  PSGenerator.Common.aesonBridge <|> PSGenerator.Common.containersBridge
    <|> PSGenerator.Common.languageBridge
    <|> PSGenerator.Common.servantBridge
    <|> PSGenerator.Common.miscBridge
    <|> doubleBridge
    <|> dayBridge
    <|> defaultBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
  languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
  []

mySettings :: Settings
mySettings =
  (defaultSettings & set apiModuleName "Marlowe")
    { _generateSubscriberAPI = False
    }

generate :: FilePath -> IO ()
generate outputDir = do
  writeAPIModuleWithSettings
    mySettings
    outputDir
    myBridgeProxy
    (Proxy @HTTPAPI)
  writePSTypesWith (defaultSwitch <> genForeign (ForeignOptions True)) outputDir (buildBridge myBridge) myTypes
