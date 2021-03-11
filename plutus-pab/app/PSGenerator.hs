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
import           Plutus.Contract.Checkpoint                 (CheckpointKey, CheckpointStore)
import           Plutus.Contract.Effects.AwaitSlot          (WaitingForSlot)
import           Plutus.Contract.Effects.AwaitTxConfirmed   (TxConfirmed)
import           Plutus.Contract.Effects.ExposeEndpoint     (ActiveEndpoint, EndpointValue)
import           Plutus.Contract.Effects.Instance           (OwnIdRequest)
import           Plutus.Contract.Effects.OwnPubKey          (OwnPubKeyRequest)
import           Plutus.Contract.Effects.UtxoAt             (UtxoAtAddress)
import           Plutus.Contract.Effects.WriteTx            (WriteTxResponse)
import           Plutus.Contract.Resumable                  (Responses)
import           Plutus.Contract.State                      (ContractRequest, State)
import           Plutus.Contracts.Currency                  (SimpleMPS (..))
import           Plutus.PAB.Core                            (activateContract, callContractEndpoint, installContract)
import           Plutus.PAB.Effects.ContractTest            (TestContracts (Currency, Game))
import           Plutus.PAB.Effects.MultiAgent              (agentAction)
import           Plutus.PAB.Events                          (ChainEvent, ContractPABRequest, csContract)
import           Plutus.PAB.Events.Contract                 (ContractEvent, ContractInstanceState, ContractResponse,
                                                             PartiallyDecodedResponse)
import           Plutus.PAB.Events.Node                     (NodeEvent)
import           Plutus.PAB.Events.User                     (UserEvent)
import           Plutus.PAB.Events.Wallet                   (WalletEvent)
import           Plutus.PAB.MockApp                         (defaultWallet)
import qualified Plutus.PAB.MockApp                         as MockApp
import           Plutus.PAB.Types                           (ContractExe)
import qualified Plutus.PAB.Webserver.API                   as API
import qualified Plutus.PAB.Webserver.Handler               as Webserver
import           Plutus.PAB.Webserver.Types                 (ChainReport, ContractReport, ContractSignatureResponse,
                                                             FullReport, StreamToClient, StreamToServer)
import           Servant.PureScript                         (HasBridge, Settings, _generateSubscriberAPI, apiModuleName,
                                                             defaultBridge, defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings)
import           System.FilePath                            ((</>))
import           Wallet.Effects                             (AddressChangeRequest (..), AddressChangeResponse (..))
import qualified Wallet.Emulator.Chain                      as Chain

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
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ChainEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @StreamToServer)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @StreamToClient)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractInstanceState A))
    , (equal <*> (genericShow <*> mkSumType))
          (Proxy @(ContractSignatureResponse A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(PartiallyDecodedResponse A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractRequest A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractPABRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UnbalancedTx)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @NodeEvent)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(UserEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WalletEvent)

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
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Plutus.PAB.Webserver")
        {_generateSubscriberAPI = False}

------------------------------------------------------------
writeTestData :: FilePath -> IO ()
writeTestData outputDir = do
    (fullReport, currencySchema) <-
        MockApp.runScenario $ do
            result <-
                agentAction defaultWallet $ do
                    installContract @TestContracts Currency
                    installContract @TestContracts Game
                    --
                    currencyInstance1 <- activateContract Currency
                    void $ activateContract Currency
                    void $ activateContract Game
                    --
                    void $
                        callContractEndpoint
                            @TestContracts
                            (csContract currencyInstance1)
                            "Create native token"
                            SimpleMPS {tokenName = "TestCurrency", amount = 10000000000}
                    --
                    report :: FullReport TestContracts <- Webserver.getFullReport
                    schema :: ContractSignatureResponse TestContracts <-
                        Webserver.contractSchema (csContract currencyInstance1)
                    pure (report, schema)
            void Chain.processBlock
            pure result
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
