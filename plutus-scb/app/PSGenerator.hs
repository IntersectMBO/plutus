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

import qualified Data.Aeson.Encode.Pretty                   as JSON
import qualified Data.ByteString.Lazy                       as BSL
import           Language.Plutus.Contract.Effects.UtxoAt    (UtxoAtAddress)
import           Language.Plutus.Contract.Effects.WriteTx   (WriteTxResponse)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Ledger.Constraints.OffChain                (UnbalancedTx)
import qualified Ledger.Index                               as Index
import           Plutus.SCB.Events                          (ChainEvent)
import           Plutus.SCB.Events.Contract                 (ContractRequest, ContractResponse, EventId, RequestEvent,
                                                             ResponseEvent)
import           Plutus.SCB.Events.Node                     (NodeEvent)
import           Plutus.SCB.Events.User                     (UserEvent)
import           Plutus.SCB.Events.Wallet                   (WalletEvent)
import           Plutus.SCB.Types                           (ActiveContract, ActiveContractState, ContractExe,
                                                             PartiallyDecodedResponse)
import qualified PSGenerator.Common
import           System.FilePath                            ((</>))

import           Control.Applicative                        ((<|>))
import           Control.Lens                               (set, (&))
import           Data.Proxy                                 (Proxy (Proxy))
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), SumType, buildBridge,
                                                             equal, genericShow, mkSumType, writePSTypesWith)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), genForeign,
                                                             unwrapSingleConstructors)
import qualified Plutus.SCB.Webserver.API                   as API
import           Plutus.SCB.Webserver.Types                 (FullReport (FullReport), annotatedBlockchain, events,
                                                             latestContractStatus, transactionMap, utxoIndex, walletMap)
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)

myBridge :: BridgePart
myBridge =
    defaultBridge <|> PSGenerator.Common.aesonBridge <|>
    PSGenerator.Common.containersBridge <|>
    PSGenerator.Common.languageBridge <|>
    PSGenerator.Common.ledgerBridge <|>
    PSGenerator.Common.servantBridge <|>
    PSGenerator.Common.miscBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    PSGenerator.Common.ledgerTypes <>
    PSGenerator.Common.walletTypes <>
    [ (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractExe)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(FullReport A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ChainEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ActiveContract A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ActiveContractState A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @PartiallyDecodedResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @EventId)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractRequest)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractResponse)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(RequestEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(ResponseEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UnbalancedTx)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @NodeEvent)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(UserEvent A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WalletEvent)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UtxoAtAddress)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WriteTxResponse)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Plutus.SCB.Webserver")
        {_generateSubscriberAPI = False}

------------------------------------------------------------
writeTestData :: FilePath -> IO ()
writeTestData outputDir = do
    let fullReport :: FullReport ContractExe =
            FullReport
                { latestContractStatus = mempty
                , events = mempty
                , transactionMap = mempty
                , utxoIndex = Index.initialise mempty
                , annotatedBlockchain = mempty
                , walletMap = mempty
                }
    BSL.writeFile
        (outputDir </> "full_report_response.json")
        (JSON.encodePretty fullReport)

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
