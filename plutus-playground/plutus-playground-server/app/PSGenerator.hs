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

import           Auth                                      (AuthRole, AuthStatus)
import qualified Auth
import           Control.Applicative                       (empty, (<|>))
import           Control.Lens                              (set, (&))
import qualified Data.ByteString                           as BS
import           Data.Monoid                               ()
import           Data.Proxy                                (Proxy (Proxy))
import qualified Data.Set                                  as Set ()
import qualified Data.Text                                 as T ()
import qualified Data.Text.Encoding                        as T ()
import qualified Data.Text.IO                              as T ()
import           Gist                                      (Gist, GistFile, Owner)
import           Language.PureScript.Bridge                (BridgePart, Language (Haskell), PSType, SumType,
                                                            TypeInfo (TypeInfo), buildBridge, equal, mkSumType,
                                                            psTypeParameters, typeModule, typeName, writePSTypes, (^==))
import           Language.PureScript.Bridge.PSTypes        (psArray, psInt, psString)
import           Language.PureScript.Bridge.TypeParameters (A)
import           Ledger.Ada                                (Ada)
import           Ledger.Index                              (ValidationError)
import           Ledger.Interval                           (Interval, Slot)
import           Ledger.Types                              (AddressOf, DataScript, PubKey, RedeemerScript, Signature,
                                                            Tx, TxIdOf, TxInOf, TxInType, TxOutOf, TxOutRefOf,
                                                            TxOutType, ValidatorScript)
import           Ledger.Value.TH                           (Value)
import           Playground.API                            (CompilationError, CompilationResult, Evaluation,
                                                            EvaluationResult, Expression, Fn, FunctionSchema,
                                                            SimpleArgumentSchema, SourceCode, Warning)
import qualified Playground.API                            as API
import           Playground.Usecases                       (crowdfunding, game, messages, vesting)
import           Servant                                   ((:<|>))
import           Servant.PureScript                        (HasBridge, Settings, apiModuleName, defaultBridge,
                                                            defaultSettings, languageBridge, writeAPIModuleWithSettings,
                                                            _generateSubscriberAPI)
import           System.FilePath                           ((</>))
import           Wallet.API                                (WalletAPIError)
import           Wallet.Emulator.Types                     (EmulatorEvent, Wallet)
import           Wallet.Graph                              (FlowGraph, FlowLink, TxRef, UtxOwner, UtxoLocation)

integerBridge :: BridgePart
integerBridge = do
  typeName ^== "Integer"
  pure psInt

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

psJson :: PSType
psJson = TypeInfo "" "Data.RawJson" "RawJson" []

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
  typeModule ^== "Ledger.Types"
  pure psString

redeemerBridge :: BridgePart
redeemerBridge = do
  typeName ^== "Redeemer"
  typeModule ^== "Ledger.Types"
  pure psString

validatorBridge :: BridgePart
validatorBridge = do
  typeName ^== "Validator"
  typeModule ^== "Ledger.Types"
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

myBridge :: BridgePart
myBridge =
  defaultBridge <|> integerBridge <|> scientificBridge <|> aesonBridge <|>
  setBridge <|>
  digestBridge <|>
  sha256Bridge <|>
  redeemerBridge <|>
  validatorBridge <|>
  scriptBridge <|>
  headersBridge <|>
  headerBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
  languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    [ mkSumType (Proxy @SimpleArgumentSchema)
    , mkSumType (Proxy @(FunctionSchema A))
    , mkSumType (Proxy @CompilationResult)
    , mkSumType (Proxy @Warning)
    , mkSumType (Proxy @Fn)
    , mkSumType (Proxy @SourceCode)
    , mkSumType (Proxy @Wallet)
    , mkSumType (Proxy @DataScript)
    , mkSumType (Proxy @ValidatorScript)
    , mkSumType (Proxy @RedeemerScript)
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
    , mkSumType (Proxy @TxInType)
    , mkSumType (Proxy @Signature)
    , mkSumType (Proxy @Value)
    , mkSumType (Proxy @PubKey)
    , mkSumType (Proxy @(AddressOf A))
    , mkSumType (Proxy @FlowLink)
    , mkSumType (Proxy @TxRef)
    , mkSumType (Proxy @UtxOwner)
    , mkSumType (Proxy @UtxoLocation)
    , mkSumType (Proxy @FlowGraph)
    , mkSumType (Proxy @(Interval A))
    , mkSumType (Proxy @Ada)
    , mkSumType (Proxy @AuthStatus)
    , mkSumType (Proxy @AuthRole)
    , mkSumType (Proxy @Gist)
    , mkSumType (Proxy @GistFile)
    , mkSumType (Proxy @Owner)
    ]

mySettings :: Settings
mySettings =
  (defaultSettings & set apiModuleName "Playground.Server")
    {_generateSubscriberAPI = False}

multilineString :: BS.ByteString -> BS.ByteString -> BS.ByteString
multilineString name value =
  "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

psModule :: BS.ByteString -> BS.ByteString -> BS.ByteString
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
  let usecases =
        multilineString "vesting" vesting <> multilineString "game" game <>
        multilineString "crowdfunding" crowdfunding <>
        multilineString "messages" messages
      usecasesModule = psModule "Playground.Usecases" usecases
  BS.writeFile (outputDir </> "Playground" </> "Usecases.purs") usecasesModule
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
  writePSTypes outputDir (buildBridge myBridge) myTypes
  writeUsecases outputDir
