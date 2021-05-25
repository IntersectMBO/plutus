{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PSGenerator
  ( generate,
  )
where

import           API                                        (ApplyInputRequest, CreateContractRequest,
                                                             GetContractHistoryResponse, GetContractStateResponse,
                                                             JSON_API, TransferRequest)
import           Control.Applicative                        ((<|>))
import           Control.Lens                               (set, (&))
import           Control.Monad.Reader                       (MonadReader)
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import qualified Data.Text.Encoding                         as T ()
import qualified Data.Text.IO                               as T ()
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), PSType, SumType,
                                                             TypeInfo (TypeInfo), buildBridge, genericShow, mkSumType,
                                                             psTypeParameters, typeModule, typeName, writePSTypesWith,
                                                             (^==))
import           Language.PureScript.Bridge.Builder         (BridgeData)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), defaultSwitch, genForeign)
import           Language.PureScript.Bridge.PSTypes         (psNumber, psString)
import qualified PSGenerator.Common
import           Servant.PureScript                         (HasBridge, Settings, _generateSubscriberAPI, apiModuleName,
                                                             defaultBridge, defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings)

psContract :: MonadReader BridgeData m => m PSType
psContract =
    TypeInfo "web-common-marlowe" "Marlowe.Semantics" "Contract" <$>
    psTypeParameters

contractBridge :: BridgePart
contractBridge = do
    typeName ^== "Contract"
    typeModule ^== "Language.Marlowe.Semantics"
    psContract

psState :: MonadReader BridgeData m => m PSType
psState =
    TypeInfo "web-common-marlowe" "Marlowe.Semantics" "State" <$>
    psTypeParameters

stateBridge :: BridgePart
stateBridge = do
    typeName ^== "State"
    typeModule ^== "Language.Marlowe.Semantics"
    psState

psTransactionInput :: MonadReader BridgeData m => m PSType
psTransactionInput =
    TypeInfo "web-common-marlowe" "Marlowe.Semantics" "TransactionInput" <$>
    psTypeParameters

transactionInputBridge :: BridgePart
transactionInputBridge = do
    typeName ^== "TransactionInput"
    typeModule ^== "Language.Marlowe.Semantics"
    psTransactionInput

psTransactionWarning :: MonadReader BridgeData m => m PSType
psTransactionWarning =
    TypeInfo "web-common-marlowe" "Marlowe.Semantics" "TransactionWarning" <$>
    psTypeParameters

transactionWarningBridge :: BridgePart
transactionWarningBridge = do
    typeName ^== "TransactionWarning"
    typeModule ^== "Language.Marlowe.Semantics"
    psTransactionWarning

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
    <|> contractBridge
    <|> stateBridge
    <|> transactionInputBridge
    <|> transactionWarningBridge
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
  [ (genericShow <*> mkSumType) (Proxy :: Proxy TransferRequest)
  , (genericShow <*> mkSumType) (Proxy :: Proxy CreateContractRequest)
  , (genericShow <*> mkSumType) (Proxy :: Proxy GetContractStateResponse)
  , (genericShow <*> mkSumType) (Proxy :: Proxy GetContractHistoryResponse)
  , (genericShow <*> mkSumType) (Proxy :: Proxy ApplyInputRequest)
  ]

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
    (Proxy @JSON_API)
  writePSTypesWith (defaultSwitch <> genForeign (ForeignOptions True)) outputDir (buildBridge myBridge) myTypes
