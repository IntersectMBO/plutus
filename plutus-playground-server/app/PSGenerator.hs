{-# LANGUAGE AutoDeriveTypeable    #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import           Control.Lens                               (set, (&))
import           Control.Monad.Reader                       (MonadReader)
import qualified Data.ByteString                            as BS
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import qualified Data.Set                                   as Set ()
import           Data.Text                                  (Text)
import qualified Data.Text                                  as T ()
import qualified Data.Text.Encoding                         as T (encodeUtf8)
import qualified Data.Text.IO                               as T ()
import           Gist                                       (Gist, GistFile, GistId, NewGist, NewGistFile, Owner)
import           Git                                        (gitRev)
import           Language.Haskell.Interpreter               (CompilationError, InterpreterError, InterpreterResult,
                                                             SourceCode, Warning)
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), PSType, SumType,
                                                             TypeInfo (TypeInfo), buildBridge, doCheck, equal,
                                                             genericShow, haskType, isTuple, mkSumType, order,
                                                             psTypeParameters, typeModule, typeName, writePSTypesWith,
                                                             (^==))
import           Language.PureScript.Bridge.Builder         (BridgeData)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), genForeign,
                                                             unwrapSingleConstructors)
import           Language.PureScript.Bridge.PSTypes         (psArray, psInt, psString)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Ledger                                     (AddressOf, DataScript, PubKey, RedeemerScript, Signature,
                                                             Tx, TxIdOf, TxInOf, TxInType, TxOutOf, TxOutRefOf,
                                                             TxOutType, ValidatorScript)
import           Ledger.Ada                                 (Ada)
import           Ledger.Index                               (ValidationError)
import           Ledger.Interval                            (Interval)
import           Ledger.Slot                                (Slot)
import           Ledger.Value                               (CurrencySymbol, TokenName, Value)
import           Playground.API                             (CompilationResult, Evaluation, EvaluationResult,
                                                             Expression, Fn, FunctionSchema, KnownCurrency, SchemaText,
                                                             SimulatorWallet)
import qualified Playground.API                             as API
import           Playground.Usecases                        (crowdfunding, game, messages, vesting)
import           Schema                                     (Label, Pair, SimpleArgumentSchema)
import           Servant                                    ((:<|>))
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)
import           System.FilePath                            ((</>))
import           Wallet.API                                 (WalletAPIError)
import           Wallet.Emulator.Types                      (EmulatorEvent, Wallet)
import           Wallet.Graph                               (FlowGraph, FlowLink, TxRef, UtxOwner, UtxoLocation)

psLedgerMap :: MonadReader BridgeData m => m PSType
psLedgerMap =
    TypeInfo "plutus-playground-client" "Ledger.Extra" "LedgerMap" <$>
    psTypeParameters

psNonEmpty :: MonadReader BridgeData m => m PSType
psNonEmpty = TypeInfo "" "Data.RawJson" "JsonNonEmptyList" <$> psTypeParameters

psJson :: PSType
psJson = TypeInfo "" "Data.RawJson" "RawJson" []

psJsonEither :: MonadReader BridgeData m => m PSType
psJsonEither = TypeInfo "" "Data.RawJson" "JsonEither" <$> psTypeParameters

psJsonTuple :: MonadReader BridgeData m => m PSType
psJsonTuple = TypeInfo "" "Data.RawJson" "JsonTuple" <$> psTypeParameters

integerBridge :: BridgePart
integerBridge = do
    typeName ^== "Integer"
    pure psInt

ledgerMapBridge :: BridgePart
ledgerMapBridge = do
    typeName ^== "Map"
    typeModule ^== "Ledger.Map"
    psLedgerMap

ledgerBytesBridge :: BridgePart
ledgerBytesBridge = do
    typeName ^== "LedgerBytes"
    typeModule ^== "LedgerBytes"
    pure psString

scientificBridge :: BridgePart
scientificBridge = do
    typeName ^== "Scientific"
    typeModule ^== "Data.Scientific"
    pure psInt

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

sha256Bridge :: BridgePart
sha256Bridge = do
    typeName ^== "SHA256"
    typeModule ^== "Crypto.Hash.Types" <|> typeModule ^== "Crypto.Hash" <|>
        typeModule ^== "Crypto.Hash.SHA256"
    pure psString

scriptBridge :: BridgePart
scriptBridge = do
    typeName ^== "Script"
    typeModule ^== "Ledger.Scripts"
    pure psString

redeemerBridge :: BridgePart
redeemerBridge = do
    typeName ^== "Redeemer"
    typeModule ^== "Ledger.Script"
    pure psString

validatorBridge :: BridgePart
validatorBridge = do
    typeName ^== "Validator"
    typeModule ^== "Ledger.Script"
    pure psString

validatorHashBridge :: BridgePart
validatorHashBridge = do
    typeName ^== "ValidatorHash"
    typeModule ^== "Ledger.Validation"
    pure psString

headersBridge :: BridgePart
headersBridge = do
    typeModule ^== "Servant.API.ResponseHeaders"
    typeName ^== "Headers"
  -- | Headers should have two parameters, the list of headers and the return type.
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

mapBridge :: BridgePart
mapBridge = do
    typeName ^== "Map"
    typeModule ^== "Data.Map.Internal"
    psLedgerMap

myBridge :: BridgePart
myBridge =
    eitherBridge <|> tupleBridge <|> defaultBridge <|> integerBridge <|>
    ledgerMapBridge <|>
    scientificBridge <|>
    aesonBridge <|>
    setBridge <|>
    digestBridge <|>
    sha256Bridge <|>
    redeemerBridge <|>
    validatorBridge <|>
    scriptBridge <|>
    headersBridge <|>
    headerBridge <|>
    nonEmptyBridge <|>
    validatorHashBridge <|>
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
    [ (equal <*> mkSumType) (Proxy @SimpleArgumentSchema)
    , (equal <*> mkSumType) (Proxy @(FunctionSchema A))
    , mkSumType (Proxy @CompilationResult)
    , (equal <*> mkSumType) (Proxy @Label)
    , (equal <*> mkSumType) (Proxy @Pair)
    , (equal <*> mkSumType) (Proxy @SchemaText)
    , mkSumType (Proxy @Warning)
    , (equal <*> mkSumType) (Proxy @Fn)
    , mkSumType (Proxy @SourceCode)
    , (equal <*> mkSumType) (Proxy @Wallet)
    , (equal <*> mkSumType) (Proxy @SimulatorWallet)
    , mkSumType (Proxy @DataScript)
    , (equal <*> (order <*> mkSumType)) (Proxy @ValidatorScript)
    , (equal <*> (order <*> mkSumType)) (Proxy @RedeemerScript)
    , (equal <*> (order <*> mkSumType)) (Proxy @Signature)
    , mkSumType (Proxy @CompilationError)
    , mkSumType (Proxy @Expression)
    , mkSumType (Proxy @Evaluation)
    , mkSumType (Proxy @EvaluationResult)
    , mkSumType (Proxy @EmulatorEvent)
    , mkSumType (Proxy @ValidationError)
    , mkSumType (Proxy @Slot)
    , mkSumType (Proxy @WalletAPIError)
    , mkSumType (Proxy @Tx)
    , mkSumType (Proxy @(TxInOf A))
    , mkSumType (Proxy @(TxOutRefOf A))
    , mkSumType (Proxy @TxOutType)
    , mkSumType (Proxy @(TxOutOf A))
    , mkSumType (Proxy @(TxIdOf A))
    , (equal <*> (order <*> mkSumType)) (Proxy @TxInType)
    , (equal <*> (order <*> mkSumType)) (Proxy @PubKey)
    , mkSumType (Proxy @(AddressOf A))
    , mkSumType (Proxy @FlowLink)
    , mkSumType (Proxy @TxRef)
    , mkSumType (Proxy @UtxOwner)
    , mkSumType (Proxy @UtxoLocation)
    , mkSumType (Proxy @FlowGraph)
    , mkSumType (Proxy @(Interval A))
    , (equal <*> mkSumType) (Proxy @Ada)
    , mkSumType (Proxy @AuthStatus)
    , mkSumType (Proxy @AuthRole)
    , (equal <*> (order <*> mkSumType)) (Proxy @GistId)
    , mkSumType (Proxy @Gist)
    , mkSumType (Proxy @GistFile)
    , mkSumType (Proxy @NewGist)
    , mkSumType (Proxy @NewGistFile)
    , mkSumType (Proxy @Owner)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Value)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @KnownCurrency)
    , mkSumType (Proxy @InterpreterError)
    , mkSumType (Proxy @(InterpreterResult A))
    , (genericShow <*> (equal <*> (order <*> mkSumType)))
          (Proxy @CurrencySymbol)
    , (genericShow <*> (equal <*> (order <*> mkSumType))) (Proxy @TokenName)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Playground.Server")
        {_generateSubscriberAPI = False}

multilineString :: Text -> Text -> Text
multilineString name value =
    "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

psModule :: Text -> Text -> Text
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let usecases =
            multilineString "gitRev" gitRev <> multilineString "vesting" vesting <>
            multilineString "game" game <>
            multilineString "crowdfunding" crowdfunding <>
            multilineString "messages" messages
        usecasesModule = psModule "Playground.Usecases" usecases
    BS.writeFile
        (outputDir </> "Playground" </> "Usecases.purs")
        (T.encodeUtf8 usecasesModule)
    putStrLn outputDir

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
