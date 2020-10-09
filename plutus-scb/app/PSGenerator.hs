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

import           Cardano.Metadata.Types                            (AnnotatedSignature, HashFunction, Property,
                                                                    PropertyKey, Subject, SubjectProperties)
import           Control.Applicative                               ((<|>))
import           Control.Lens                                      (set, view, (&))
import           Control.Monad                                     (void)
import           Control.Monad.Freer.Log                           (LogLevel, LogMessage)
import qualified Data.Aeson.Encode.Pretty                          as JSON
import qualified Data.ByteString.Lazy                              as BSL
import           Data.Proxy                                        (Proxy (Proxy))
import           Language.Plutus.Contract.Checkpoint               (CheckpointKey, CheckpointStore)
import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot)
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed)
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint, EndpointValue)
import           Language.Plutus.Contract.Effects.Instance         (OwnIdRequest)
import           Language.Plutus.Contract.Effects.OwnPubKey        (OwnPubKeyRequest)
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress)
import           Language.Plutus.Contract.Effects.WriteTx          (WriteTxResponse)
import           Language.Plutus.Contract.Resumable                (Request, RequestID, Response, Responses)
import           Language.Plutus.Contract.State                    (ContractRequest, State)
import           Language.PlutusTx.Coordination.Contracts.Currency (SimpleMPS (..))
import           Language.PureScript.Bridge                        (BridgePart, Language (Haskell), SumType,
                                                                    TypeInfo (TypeInfo), buildBridge, equal,
                                                                    genericShow, haskType, mkSumType, order, typeModule,
                                                                    typeName, writePSTypesWith, (^==))
import           Language.PureScript.Bridge.CodeGenSwitches        (ForeignOptions (ForeignOptions), genForeign,
                                                                    unwrapSingleConstructors)
import           Language.PureScript.Bridge.TypeParameters         (A)
import           Ledger.Constraints.OffChain                       (UnbalancedTx)
import           Plutus.SCB.Core                                   (activateContract, callContractEndpoint,
                                                                    installContract)
import           Plutus.SCB.Effects.ContractTest                   (TestContracts (Currency, Game))
import           Plutus.SCB.Effects.MultiAgent                     (agentAction)
import           Plutus.SCB.Events                                 (ChainEvent, ContractSCBRequest, csContract)
import           Plutus.SCB.Events.Contract                        (ContractEvent, ContractInstanceState,
                                                                    ContractResponse, IterationID,
                                                                    PartiallyDecodedResponse)
import           Plutus.SCB.Events.Node                            (NodeEvent)
import           Plutus.SCB.Events.User                            (UserEvent)
import           Plutus.SCB.Events.Wallet                          (WalletEvent)
import           Plutus.SCB.MockApp                                (defaultWallet, syncAll)
import qualified Plutus.SCB.MockApp                                as MockApp
import           Plutus.SCB.Types                                  (ContractExe)
import qualified Plutus.SCB.Webserver.API                          as API
import qualified Plutus.SCB.Webserver.Handler                      as Webserver
import           Plutus.SCB.Webserver.Types                        (ChainReport, ContractReport,
                                                                    ContractSignatureResponse, FullReport,
                                                                    StreamToClient, StreamToServer)
import qualified PSGenerator.Common
import           Servant.PureScript                                (HasBridge, Settings, apiModuleName, defaultBridge,
                                                                    defaultSettings, languageBridge,
                                                                    writeAPIModuleWithSettings, _generateSubscriberAPI)
import           System.FilePath                                   ((</>))
import           Wallet.Effects                                    (AddressChangeRequest (..),
                                                                    AddressChangeResponse (..))
import qualified Wallet.Emulator.Chain                             as Chain

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
  pure $ TypeInfo "plutus-scb" moduleName name []

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
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractSCBRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ContractEvent A))
    , (order <*> (genericShow <*> mkSumType)) (Proxy @IterationID)
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
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(Response A))
    , (order <*> (genericShow <*> mkSumType)) (Proxy @RequestID)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(Request A))
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
    (defaultSettings & set apiModuleName "Plutus.SCB.Webserver")
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
            syncAll
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
