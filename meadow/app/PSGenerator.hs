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

import           API                                        (RunResult)
import qualified API
import           Auth                                       (AuthRole, AuthStatus)
import qualified Auth
import           Control.Applicative                        (empty, (<|>))
import           Control.Lens                               (set, (&))
import           Control.Monad.Reader                       (MonadReader)
import qualified Data.ByteString                            as BS
import qualified Data.ByteString.Char8                      as CBS
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import qualified Data.Set                                   as Set ()
import qualified Data.Text                                  as T (unpack)
import qualified Data.Text.Encoding                         as T ()
import qualified Data.Text.IO                               as T ()
import           Gist                                       (Gist, GistFile, GistId, NewGist, NewGistFile, Owner)
import           Git                                        (gitRev)
import           Language.Haskell.Interpreter               (CompilationError, InterpreterError, InterpreterResult,
                                                             SourceCode, Warning)
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), PSType, SumType,
                                                             TypeInfo (TypeInfo), buildBridge, doCheck, haskType,
                                                             isTuple, mkSumType, psTypeParameters, typeModule, typeName,
                                                             writePSTypesWith, (^==))
import           Language.PureScript.Bridge.Builder         (BridgeData)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), defaultSwitch, genForeign)
import           Language.PureScript.Bridge.PSTypes         (psArray, psInt)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Meadow.Contracts                           (couponBondGuaranteed, escrow, zeroCouponBond)
import           Servant                                    ((:<|>))
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)
import           System.Directory                           (createDirectoryIfMissing)
import           System.FilePath                            ((</>))

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

myBridge :: BridgePart
myBridge =
    eitherBridge <|> tupleBridge <|>
    defaultBridge <|> integerBridge <|> scientificBridge <|> aesonBridge <|>
    setBridge <|>
    headersBridge <|>
    headerBridge <|>
    nonEmptyBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    [ mkSumType (Proxy @RunResult)
    , mkSumType (Proxy @SourceCode)
    , mkSumType (Proxy @CompilationError)
    , mkSumType (Proxy @InterpreterError)
    , mkSumType (Proxy @AuthStatus)
    , mkSumType (Proxy @AuthRole)
    , mkSumType (Proxy @GistId)
    , mkSumType (Proxy @Gist)
    , mkSumType (Proxy @GistFile)
    , mkSumType (Proxy @NewGist)
    , mkSumType (Proxy @NewGistFile)
    , mkSumType (Proxy @Owner)
    , mkSumType (Proxy @Warning)
    , mkSumType (Proxy @(InterpreterResult A))
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Meadow")
        {_generateSubscriberAPI = False}

multilineString :: BS.ByteString -> BS.ByteString -> BS.ByteString
multilineString name value =
    "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

psModule :: BS.ByteString -> BS.ByteString -> BS.ByteString
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let usecases =
            multilineString "gitRev" (CBS.pack . T.unpack $ gitRev)
         <> multilineString "escrow" escrow
         <> multilineString "zeroCouponBond" zeroCouponBond
         <> multilineString "couponBondGuaranteed" couponBondGuaranteed
        usecasesModule = psModule "Meadow.Contracts" usecases
    createDirectoryIfMissing True (outputDir </> "Meadow")
    BS.writeFile (outputDir </> "Meadow" </> "Contracts.purs") usecasesModule
    putStrLn outputDir

generate :: FilePath -> IO ()
generate outputDir = do
    writeAPIModuleWithSettings
        mySettings
        outputDir
        myBridgeProxy
        (Proxy @(API.API :<|> Auth.FrontendAPI))
    writePSTypesWith (defaultSwitch <> genForeign (ForeignOptions True)) outputDir (buildBridge myBridge) myTypes
    writeUsecases outputDir
