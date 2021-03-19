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

module PSGenerator
    ( generate
    ) where

import           Cardano.Metadata.Types                     (AnnotatedSignature, HashFunction, Property, PropertyKey,
                                                             Subject, SubjectProperties)
import           Control.Applicative                        ((<|>))
import           Control.Lens                               (set, view, (&))
import           Control.Monad                              (void)
import           Control.Monad.Freer.Extras.Log             (LogLevel, LogMessage)
import qualified Data.Aeson.Encode.Pretty                   as JSON
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Proxy                                 (Proxy (Proxy))
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), SumType,
                                                             TypeInfo (TypeInfo), buildBridge, equal, genericShow,
                                                             haskType, mkSumType, order, typeModule, typeName,
                                                             writePSTypesWith, (^==))
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), genForeign,
                                                             unwrapSingleConstructors)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Ledger.Constraints.OffChain                (UnbalancedTx)
import qualified PSGenerator.Common
import           Plutus.PAB.Effects.Contract.ContractExe           (ContractExe)
import           Plutus.PAB.Effects.Contract.ContractTest          (TestContracts (Currency, Game))
import           Plutus.PAB.Events.Contract                        (ContractPABRequest, ContractResponse)
import           Plutus.PAB.Events.ContractInstanceState           (PartiallyDecodedResponse)
import qualified Plutus.PAB.Simulator                              as Simulator
import qualified Plutus.PAB.Webserver.API                          as API
import qualified Plutus.PAB.Webserver.Handler                      as Webserver
import           Plutus.PAB.Webserver.Types                        (ChainReport, ContractReport,
                                                                    ContractSignatureResponse, FullReport,
                                                                    StreamToClient, StreamToServer)
import           Servant.PureScript                                (HasBridge, Settings, _generateSubscriberAPI,
                                                                    apiModuleName, defaultBridge, defaultSettings,
                                                                    languageBridge, writeAPIModuleWithSettings)
import           System.FilePath                                   ((</>))
import           Wallet.Effects                                    (AddressChangeRequest (..),
                                                                    AddressChangeResponse (..))
import           Wallet.Emulator.Wallet                            (Wallet (..))

myBridge :: BridgePart
myBridge =
    PSGenerator.Common.aesonBridge <|>
    PSGenerator.Common.containersBridge <|>
    PSGenerator.Common.languageBridge <|>
    PSGenerator.Common.ledgerBridge <|>
    PSGenerator.Common.servantBridge <|>
    PSGenerator.Common.miscBridge <|>
    metadataBridge <|>
    defaultBridge

-- Some of the metadata types have a datakind type parameter that
-- PureScript won't support, so we must drop it.
metadataBridge :: BridgePart
metadataBridge = do
  (typeName ^== "Property")
    <|> (typeName ^== "SubjectProperties")
    <|> (typeName ^== "AnnotatedSignature")
  typeModule ^== "Cardano.Metadata.Types"
  moduleName <- view (haskType . typeModule)
  name <- view (haskType . typeName)
  pure $ TypeInfo "plutus-pab" moduleName name []

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    PSGenerator.Common.ledgerTypes <>
    PSGenerator.Common.playgroundTypes <>
    PSGenerator.Common.walletTypes <>
    [ (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractExe)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TestContracts)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(FullReport A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ChainReport)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractReport A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @StreamToServer)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @StreamToClient)
    , (equal <*> (genericShow <*> mkSumType))
          (Proxy @(ContractSignatureResponse A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(PartiallyDecodedResponse A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractRequest A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractPABRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UnbalancedTx)

    -- Contract request / response types
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ActiveEndpoint)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(EndpointValue A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @OwnPubKeyRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxConfirmed)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UtxoAtAddress)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WriteTxResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WaitingForSlot)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(State A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @CheckpointStore)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @CheckpointKey)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(Responses A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @AddressChangeRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @AddressChangeResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @OwnIdRequest)

    -- Logging types
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(LogMessage A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @LogLevel)

    -- Metadata types
    , (order <*> (genericShow <*> mkSumType)) (Proxy @Subject)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(SubjectProperties A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(Property A))
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PropertyKey)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @HashFunction)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(AnnotatedSignature A))

    -- * Web API types
    , (genericShow <*> mkSumType) (Proxy @API.WalletInfo)
    , (genericShow <*> mkSumType) (Proxy @(API.ContractActivationArgs A))
    , (genericShow <*> mkSumType) (Proxy @API.ContractInstanceClientState)
    , (genericShow <*> mkSumType) (Proxy @API.InstanceStatusToClient)
    , (genericShow <*> mkSumType) (Proxy @API.CombinedWSStreamToClient)
    , (genericShow <*> mkSumType) (Proxy @API.CombinedWSStreamToServer)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Plutus.PAB.Webserver")
        {_generateSubscriberAPI = False}

defaultWallet :: Wallet
defaultWallet = Wallet 1

------------------------------------------------------------
writeTestData :: FilePath -> IO ()
writeTestData outputDir = do
    (fullReport, currencySchema) <-
        fmap (either (error . show) id) $ Simulator.runSimulation $ do
            currencyInstance1 <- Simulator.activateContract defaultWallet Currency
            void $ Simulator.activateContract defaultWallet Currency
            void $ Simulator.activateContract defaultWallet Game
            void $ Simulator.callEndpointOnInstance currencyInstance1 "Create native token" SimpleMPS {tokenName = "TestCurrency", amount = 10000000000}
            void $ Simulator.waitUntilFinished currencyInstance1
            report :: FullReport TestContracts <- Webserver.getFullReport
            schema :: ContractSignatureResponse TestContracts <- Webserver.contractSchema currencyInstance1
            pure (report, schema)
    BSL.writeFile
        (outputDir </> "full_report_response.json")
        (JSON.encodePretty fullReport)
    BSL.writeFile
        (outputDir </> "contract_schema_response.json")
        (JSON.encodePretty currencySchema)

------------------------------------------------------------
generate :: FilePath -> IO ()
generate outputDir = do
    writeAPIModuleWithSettings
        mySettings
        outputDir
        myBridgeProxy
        (Proxy @(API.API ContractExe))
    writePSTypesWith
        (genForeign (ForeignOptions {unwrapSingleConstructors = True}))
        outputDir
        (buildBridge myBridge)
        myTypes
    writeTestData outputDir
    putStrLn $ "Done: " <> outputDir
