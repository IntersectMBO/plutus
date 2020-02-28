{-# LANGUAGE AutoDeriveTypeable    #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module PSGenerator
    ( generate
    ) where

import           Auth                                       (AuthRole, AuthStatus)
import qualified Auth
import           Control.Applicative                        (empty, (<|>))
import           Control.Lens                               (itraverse, set, (&))
import           Control.Monad                              (void)
import           Control.Monad.Catch                        (MonadMask)
import           Control.Monad.Except                       (MonadError, runExceptT)
import           Control.Monad.IO.Class                     (MonadIO)
import           Control.Monad.Reader                       (MonadReader)
import qualified Crowdfunding
import qualified CrowdfundingSimulations
import           Data.Aeson                                 (ToJSON, toJSON)
import qualified Data.Aeson                                 as JSON
import qualified Data.Aeson.Encode.Pretty                   as JSON
import qualified Data.ByteString                            as BS
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import           Data.Text                                  (Text)
import qualified Data.Text.Encoding                         as T (decodeUtf8, encodeUtf8)
import           Data.Time.Units                            (Second)
import qualified ErrorHandling
import qualified ErrorHandlingSimulations
import qualified Game
import qualified GameSimulations
import           Gist                                       (Gist, GistFile, GistId, NewGist, NewGistFile, Owner)
import           Language.Haskell.Interpreter               (CompilationError, InterpreterError,
                                                             InterpreterResult (InterpreterResult),
                                                             SourceCode (SourceCode), Warning, result, warnings)
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), PSType, SumType,
                                                             TypeInfo (TypeInfo), buildBridge, doCheck, equal, equal1,
                                                             functor, genericShow, haskType, isTuple, mkSumType, order,
                                                             psTypeParameters, typeModule, typeName, writePSTypesWith,
                                                             (^==))
import           Language.PureScript.Bridge.Builder         (BridgeData)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), genForeign,
                                                             unwrapSingleConstructors)
import           Language.PureScript.Bridge.PSTypes         (psArray, psInt, psString)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Ledger                                     (Address, DataValue, MonetaryPolicy, PubKey, PubKeyHash,
                                                             RedeemerValue, Signature, Tx, TxId, TxIn, TxInType, TxOut,
                                                             TxOutRef, TxOutType, Validator)
import           Ledger.Ada                                 (Ada)
import           Ledger.Index                               (ValidationError)
import           Ledger.Interval                            (Extended, Interval, LowerBound, UpperBound)
import           Ledger.Scripts                             (ScriptError)
import           Ledger.Slot                                (Slot)
import           Ledger.Value                               (CurrencySymbol, TokenName, Value)
import qualified Playground.API                             as API
import qualified Playground.Interpreter                     as PI
import           Playground.Types                           (CompilationResult (CompilationResult), ContractCall,
                                                             ContractDemo (ContractDemo), EndpointName,
                                                             Evaluation (Evaluation), EvaluationResult, FunctionSchema,
                                                             KnownCurrency, PlaygroundError, Simulation (Simulation),
                                                             SimulatorAction, SimulatorWallet, contractDemoContext,
                                                             contractDemoEditorContents, contractDemoName,
                                                             contractDemoSimulations, functionSchema, iotsSpec,
                                                             knownCurrencies, program, simulationActions,
                                                             simulationWallets, sourceCode, wallets)
import           Playground.Usecases                        (crowdFunding, errorHandling, game, starter, vesting)
import qualified Playground.Usecases                        as Usecases
import           Schema                                     (FormArgumentF, FormSchema, formArgumentToJson)
import           Servant                                    ((:<|>))
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)
import qualified Starter
import qualified StarterSimulations
import           System.FilePath                            ((</>))
import qualified Vesting
import qualified VestingSimulations
import           Wallet.API                                 (WalletAPIError)
import qualified Wallet.Emulator.Chain                      as EM
import qualified Wallet.Emulator.ChainIndex                 as EM
import qualified Wallet.Emulator.MultiAgent                 as EM
import qualified Wallet.Emulator.NodeClient                 as EM
import qualified Wallet.Emulator.Wallet                     as EM
import           Wallet.Rollup.Types                        (AnnotatedTx, BeneficialOwner, DereferencedInput,
                                                             SequenceId)

psAssocMap :: MonadReader BridgeData m => m PSType
psAssocMap =
    TypeInfo "plutus-playground-client" "Language.PlutusTx.AssocMap" "Map" <$>
    psTypeParameters

psJson :: PSType
psJson = TypeInfo "" "Data.RawJson" "RawJson" []

psNonEmpty :: MonadReader BridgeData m => m PSType
psNonEmpty =
    TypeInfo "" "Data.Json.JsonNonEmptyList" "JsonNonEmptyList" <$>
    psTypeParameters

psJsonEither :: MonadReader BridgeData m => m PSType
psJsonEither =
    TypeInfo "" "Data.Json.JsonEither" "JsonEither" <$> psTypeParameters

psJsonTuple :: MonadReader BridgeData m => m PSType
psJsonTuple = TypeInfo "" "Data.Json.JsonTuple" "JsonTuple" <$> psTypeParameters

integerBridge :: BridgePart
integerBridge = do
    typeName ^== "Integer"
    pure psInt

dataBridge :: BridgePart
dataBridge = do
    typeName ^== "Data"
    typeModule ^== "Language.PlutusTx.Data"
    pure psString

assocMapBridge :: BridgePart
assocMapBridge = do
    typeName ^== "Map"
    typeModule ^== "Language.PlutusTx.AssocMap"
    psAssocMap

ledgerBytesBridge :: BridgePart
ledgerBytesBridge = do
    typeName ^== "LedgerBytes"
    typeModule ^== "LedgerBytes"
    pure psString

aesonBridge :: BridgePart
aesonBridge = do
    typeName ^== "Value"
    typeModule ^== "Data.Aeson.Types.Internal"
    pure psJson

eitherBridge :: BridgePart
eitherBridge = do
    typeName ^== "Either"
    psJsonEither

tupleBridge :: BridgePart
tupleBridge = do
    doCheck haskType isTuple
    psJsonTuple

setBridge :: BridgePart
setBridge = do
    typeName ^== "Set"
    typeModule ^== "Data.Set" <|> typeModule ^== "Data.Set.Internal"
    psArray

digestBridge :: BridgePart
digestBridge = do
    typeName ^== "Digest"
    typeModule ^== "Crypto.Hash.Types"
    pure psString

scriptBridge :: BridgePart
scriptBridge = do
    typeName ^== "Script"
    typeModule ^== "Ledger.Scripts"
    pure psString

validatorHashBridge :: BridgePart
validatorHashBridge = do
    typeName ^== "ValidatorHash"
    typeModule ^== "Ledger.Scripts"
    pure psString

mpsHashBridge :: BridgePart
mpsHashBridge = do
    typeName ^== "MonetaryPolicyHash"
    typeModule ^== "Ledger.Scripts"
    pure psString

dataHashBridge :: BridgePart
dataHashBridge = do
    typeName ^== "DataValueHash"
    typeModule ^== "Ledger.Scripts"
    pure psString

headersBridge :: BridgePart
headersBridge = do
    typeModule ^== "Servant.API.ResponseHeaders"
    typeName ^== "Headers"
    -- Headers should have two parameters, the list of headers and the return type.
    psTypeParameters >>= \case
        [_, returnType] -> pure returnType
        _ -> empty

headerBridge :: BridgePart
headerBridge = do
    typeModule ^== "Servant.API.Header"
    typeName ^== "Header'"
    empty

nonEmptyBridge :: BridgePart
nonEmptyBridge = do
    typeName ^== "NonEmpty"
    typeModule ^== "GHC.Base"
    psNonEmpty

byteStringBridge :: BridgePart
byteStringBridge = do
    typeName ^== "ByteString"
    typeModule ^== "Data.ByteString.Lazy.Internal"
    pure psString

-- | We represent 'Map' using an 'AssocMap'. It's not ideal, but it's
-- a fair way of representing JSON if your keys don't always have a
-- natural string representation.
mapBridge :: BridgePart
mapBridge = do
    typeName ^== "Map"
    typeModule ^== "Data.Map.Internal"
    psAssocMap

myBridge :: BridgePart
myBridge =
    eitherBridge <|> tupleBridge <|> defaultBridge <|> integerBridge <|>
    assocMapBridge <|>
    aesonBridge <|>
    setBridge <|>
    digestBridge <|>
    dataBridge <|>
    scriptBridge <|>
    headersBridge <|>
    headerBridge <|>
    nonEmptyBridge <|>
    validatorHashBridge <|>
    mpsHashBridge <|>
    dataHashBridge <|>
    byteStringBridge <|>
    mapBridge <|>
    ledgerBytesBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    [ (genericShow <*> (equal <*> mkSumType)) (Proxy @FormSchema)
    , (functor <*> (genericShow <*> (equal <*> mkSumType)))
          (Proxy @(FunctionSchema A))
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @CompilationResult)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Warning)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @EndpointName)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @SourceCode)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @EM.Wallet)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Simulation)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @ContractDemo)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @(ContractCall A))
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @SimulatorWallet)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @DataValue)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Validator)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @MonetaryPolicy)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @RedeemerValue)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Signature)
    , (genericShow <*> mkSumType) (Proxy @CompilationError)
    , (functor <*> (equal <*> (equal1 <*> (genericShow <*> mkSumType))))
          (Proxy @(FormArgumentF A))
    , (genericShow <*> mkSumType) (Proxy @Evaluation)
    , (genericShow <*> mkSumType) (Proxy @EvaluationResult)
    , (genericShow <*> mkSumType) (Proxy @EM.EmulatorEvent)
    , (genericShow <*> mkSumType) (Proxy @EM.ChainEvent)
    , (genericShow <*> mkSumType) (Proxy @EM.WalletEvent)
    , (genericShow <*> mkSumType) (Proxy @EM.NodeClientEvent)
    , (genericShow <*> mkSumType) (Proxy @EM.ChainIndexEvent)
    , (genericShow <*> mkSumType) (Proxy @PlaygroundError)
    , (genericShow <*> mkSumType) (Proxy @ValidationError)
    , (genericShow <*> mkSumType) (Proxy @ScriptError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Slot)
    , (genericShow <*> mkSumType) (Proxy @WalletAPIError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Tx)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @SequenceId)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @AnnotatedTx)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @DereferencedInput)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @BeneficialOwner)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxId)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxIn)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxOut)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxOutRef)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @TxInType)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxOutType)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PubKey)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PubKeyHash)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @Address)
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(Interval A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(LowerBound A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(UpperBound A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(Extended A))
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Ada)
    , mkSumType (Proxy @AuthStatus)
    , mkSumType (Proxy @AuthRole)
    , (order <*> mkSumType) (Proxy @GistId)
    , mkSumType (Proxy @Gist)
    , mkSumType (Proxy @GistFile)
    , mkSumType (Proxy @NewGist)
    , mkSumType (Proxy @NewGistFile)
    , mkSumType (Proxy @Owner)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Value)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @KnownCurrency)
    , (genericShow <*> mkSumType) (Proxy @InterpreterError)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @(InterpreterResult A))
    , (genericShow <*> (order <*> mkSumType)) (Proxy @CurrencySymbol)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @TokenName)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Playground.Server")
        {_generateSubscriberAPI = False}

multilineString :: Text -> Text -> Text
multilineString name value =
    "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

jsonExport :: ToJSON a => Text -> a -> Text
jsonExport name value =
    multilineString name (T.decodeUtf8 . BSL.toStrict $ JSON.encodePretty value)

sourceCodeExport :: Text -> SourceCode -> Text
sourceCodeExport name (SourceCode value) = multilineString name value

psModule :: Text -> Text -> Text
psModule name body = "module " <> name <> " where" <> body

------------------------------------------------------------
writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let usecases =
            sourceCodeExport "vesting" vesting <> sourceCodeExport "game" game <>
            sourceCodeExport "crowdFunding" crowdFunding <>
            sourceCodeExport "errorHandling" errorHandling <>
            sourceCodeExport "starter" starter <>
            jsonExport "contractDemos" contractDemos
        usecasesModule = psModule "Playground.Usecases" usecases
    BS.writeFile
        (outputDir </> "Playground" </> "Usecases.purs")
        (T.encodeUtf8 usecasesModule)

------------------------------------------------------------
writeTestData :: FilePath -> IO ()
writeTestData outputDir = do
    let ContractDemo { contractDemoContext
                     , contractDemoSimulations
                     , contractDemoEditorContents
                     } = head contractDemos
    BSL.writeFile
        (outputDir </> "compilation_response.json")
        (JSON.encodePretty contractDemoContext)
    void $
        itraverse
            (\index ->
                 writeSimulation
                     (outputDir </> "evaluation_response" <> show index <>
                      ".json")
                     contractDemoEditorContents)
            contractDemoSimulations

writeSimulation :: FilePath -> SourceCode -> Simulation -> IO ()
writeSimulation filename sourceCode simulation = do
    result <- runExceptT $ runSimulation sourceCode simulation
    case result of
        Left err   -> fail $ "Error evaluating simulation: " <> show err
        Right json -> BSL.writeFile filename json

maxInterpretationTime :: Second
maxInterpretationTime = 80

runSimulation ::
       (MonadMask m, MonadError PlaygroundError m, MonadIO m)
    => SourceCode
    -> Simulation
    -> m BSL.ByteString
runSimulation sourceCode Simulation {simulationActions, simulationWallets} = do
    let evaluation =
            Evaluation
                { sourceCode
                , wallets = simulationWallets
                , program =
                      toJSON . encodeToText $ toExpression <$> simulationActions
                }
    interpreterResult <- PI.evaluateSimulation maxInterpretationTime evaluation
    pure $ JSON.encodePretty interpreterResult

encodeToText :: ToJSON a => a -> Text
encodeToText = T.decodeUtf8 . BSL.toStrict . JSON.encode

toExpression :: SimulatorAction -> Maybe (ContractCall Text)
toExpression = traverse (fmap encodeToText . formArgumentToJson)

------------------------------------------------------------
generate :: FilePath -> IO ()
generate outputDir = do
    writeAPIModuleWithSettings
        mySettings
        outputDir
        myBridgeProxy
        (Proxy
             @(API.API
               :<|> Auth.FrontendAPI))
    writePSTypesWith
        (genForeign (ForeignOptions {unwrapSingleConstructors = True}))
        outputDir
        (buildBridge myBridge)
        myTypes
    writeUsecases outputDir
    writeTestData outputDir
    putStrLn $ "Done: " <> outputDir

------------------------------------------------------------
contractDemos :: [ContractDemo]
contractDemos =
    [ mkContractDemo
          "Starter"
          Usecases.starter
          StarterSimulations.simulations
          Starter.schemas
          Starter.registeredKnownCurrencies
    , mkContractDemo
          "Game"
          Usecases.game
          GameSimulations.simulations
          Game.schemas
          Game.registeredKnownCurrencies
    , mkContractDemo
          "Vesting"
          Usecases.vesting
          VestingSimulations.simulations
          Vesting.schemas
          Vesting.registeredKnownCurrencies
    , mkContractDemo
          "Crowd Funding"
          Usecases.crowdFunding
          CrowdfundingSimulations.simulations
          Crowdfunding.schemas
          Crowdfunding.registeredKnownCurrencies
    , mkContractDemo
          "Error Handling"
          Usecases.errorHandling
          ErrorHandlingSimulations.simulations
          ErrorHandling.schemas
          ErrorHandling.registeredKnownCurrencies
    ]

mkContractDemo ::
       Text
    -> SourceCode
    -> [Simulation]
    -> [FunctionSchema FormSchema]
    -> [KnownCurrency]
    -> ContractDemo
mkContractDemo contractDemoName contractDemoEditorContents contractDemoSimulations functionSchema knownCurrencies =
    ContractDemo
        { contractDemoName
        , contractDemoEditorContents
        , contractDemoSimulations
        , contractDemoContext =
              InterpreterResult
                  { warnings = []
                  , result =
                        CompilationResult
                            {functionSchema, knownCurrencies, iotsSpec = ""}
                  }
        }
