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
import           Language.Haskell.Interpreter               (CompilationError, InterpreterError, InterpreterResult,
                                                             SourceCode, Warning)
import           Language.PlutusTx                          (Data)
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), PSType, SumType,
                                                             TypeInfo (TypeInfo), buildBridge, doCheck, equal, functor,
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
import           Ledger.Interval                            (Extended, Interval, LowerBound, UpperBound)
import           Ledger.Scripts                             (ScriptError)
import           Ledger.Slot                                (Slot)
import           Ledger.Value                               (CurrencySymbol, TokenName, Value)
import qualified Playground.API                             as API
import           Playground.Types                           (AnnotatedTx, BeneficialOwner, CompilationResult,
                                                             DereferencedInput, Evaluation, EvaluationResult,
                                                             Expression, Fn, FunctionSchema, KnownCurrency,
                                                             PlaygroundError, SequenceId, SimulatorWallet)
import           Playground.Usecases                        (crowdfunding, game, messages, starter, vesting)
import           Schema                                     (FormSchema)
import           Servant                                    ((:<|>))
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)
import           System.FilePath                            ((</>))
import           Wallet.API                                 (WalletAPIError)
import           Wallet.Emulator.Types                      (EmulatorEvent, Wallet)

psAssocMap :: MonadReader BridgeData m => m PSType
psAssocMap =
    TypeInfo "plutus-playground-client" "Language.PlutusTx.AssocMap" "Map" <$>
    psTypeParameters

psJson :: PSType
psJson = TypeInfo "" "Data.RawJson" "RawJson" []

psNonEmpty :: MonadReader BridgeData m => m PSType
psNonEmpty = TypeInfo "" "Data.Json.JsonNonEmptyList" "JsonNonEmptyList" <$> psTypeParameters

psJsonEither :: MonadReader BridgeData m => m PSType
psJsonEither = TypeInfo "" "Data.Json.JsonEither" "JsonEither" <$> psTypeParameters

psJsonTuple :: MonadReader BridgeData m => m PSType
psJsonTuple = TypeInfo "" "Data.Json.JsonTuple" "JsonTuple" <$> psTypeParameters

integerBridge :: BridgePart
integerBridge = do
    typeName ^== "Integer"
    pure psInt

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
    [ (genericShow <*> (equal <*> mkSumType)) (Proxy @FormSchema)
    , (functor <*> (genericShow <*> (equal <*> mkSumType)))
          (Proxy @(FunctionSchema A))
    , (genericShow <*> mkSumType) (Proxy @CompilationResult)
    , (genericShow <*> mkSumType) (Proxy @Warning)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Fn)
    , (genericShow <*> mkSumType) (Proxy @SourceCode)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @Wallet)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @SimulatorWallet)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @DataScript)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @ValidatorScript)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @RedeemerScript)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Signature)
    , (genericShow <*> mkSumType) (Proxy @CompilationError)
    , (genericShow <*> mkSumType) (Proxy @Expression)
    , (genericShow <*> mkSumType) (Proxy @Evaluation)
    , (genericShow <*> mkSumType) (Proxy @EvaluationResult)
    , (genericShow <*> mkSumType) (Proxy @EmulatorEvent)
    , (genericShow <*> mkSumType) (Proxy @PlaygroundError)
    , (genericShow <*> mkSumType) (Proxy @ValidationError)
    , (genericShow <*> mkSumType) (Proxy @ScriptError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Slot)
    , (genericShow <*> mkSumType) (Proxy @WalletAPIError)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @Data)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Tx)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @SequenceId)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @AnnotatedTx)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @DereferencedInput)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @BeneficialOwner)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(TxIdOf A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(TxInOf A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(TxOutOf A))
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @(TxOutRefOf A))
    , (genericShow <*> (order <*> mkSumType)) (Proxy @TxInType)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxOutType)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PubKey)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @(AddressOf A))
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
    , (genericShow <*> mkSumType) (Proxy @(InterpreterResult A))
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

psModule :: Text -> Text -> Text
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let usecases =
            multilineString "vesting" vesting <> multilineString "game" game <>
            multilineString "crowdfunding" crowdfunding <>
            multilineString "messages" messages <>
            multilineString "starter" starter
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
