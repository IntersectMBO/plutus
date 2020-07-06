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
import qualified Auth
import           Control.Applicative                        ((<|>))
import           Control.Lens                               (set, (&))
import qualified Data.ByteString                            as BS
import qualified Data.ByteString.Char8                      as BS8
import           Data.Monoid                                ()
import           Data.Proxy                                 (Proxy (Proxy))
import qualified Data.Set                                   as Set ()
import qualified Data.Text.Encoding                         as T ()
import qualified Data.Text.IO                               as T ()
import qualified Escrow
import           Language.Haskell.Interpreter               (CompilationError, InterpreterError, InterpreterResult,
                                                             SourceCode, Warning)
import           Language.Marlowe.Pretty                    (pretty)
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), SumType, buildBridge,
                                                             mkSumType, writePSTypesWith)
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (ForeignOptions), defaultSwitch, genForeign)
import           Language.PureScript.Bridge.TypeParameters  (A)
import           Marlowe.Contracts                          (couponBondGuaranteed, escrow, swap, zeroCouponBond)
import qualified Marlowe.Symbolic.Types.Request             as MSReq
import qualified Marlowe.Symbolic.Types.Response            as MSRes
import qualified Option
import qualified PSGenerator.Common
import           Servant                                    ((:<|>))
import           Servant.PureScript                         (HasBridge, Settings, apiModuleName, defaultBridge,
                                                             defaultSettings, languageBridge,
                                                             writeAPIModuleWithSettings, _generateSubscriberAPI)
import qualified Swap
import           System.Directory                           (createDirectoryIfMissing)
import           System.FilePath                            ((</>))
import           WebSocket                                  (WebSocketRequestMessage, WebSocketResponseMessage)
import qualified ZeroCouponBond

myBridge :: BridgePart
myBridge =
    PSGenerator.Common.aesonBridge <|> PSGenerator.Common.containersBridge <|>
    PSGenerator.Common.languageBridge <|>
    PSGenerator.Common.ledgerBridge <|>
    PSGenerator.Common.servantBridge <|>
    PSGenerator.Common.miscBridge <|>
    defaultBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    PSGenerator.Common.ledgerTypes <>
    PSGenerator.Common.walletTypes <>
    PSGenerator.Common.playgroundTypes <>
    [ mkSumType (Proxy @RunResult)
    , mkSumType (Proxy @SourceCode)
    , mkSumType (Proxy @CompilationError)
    , mkSumType (Proxy @InterpreterError)
    , mkSumType (Proxy @Warning)
    , mkSumType (Proxy @(InterpreterResult A))
    , mkSumType (Proxy @MSRes.Response)
    , mkSumType (Proxy @MSRes.Result)
    , mkSumType (Proxy @MSReq.Request)
    , mkSumType (Proxy @WebSocketRequestMessage)
    , mkSumType (Proxy @WebSocketResponseMessage)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Marlowe")
        {_generateSubscriberAPI = False}

multilineString :: BS.ByteString -> BS.ByteString -> BS.ByteString
multilineString name value =
    "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

psModule :: BS.ByteString -> BS.ByteString -> BS.ByteString
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let haskellUsecases =
            multilineString "escrow" escrow
         <> multilineString "zeroCouponBond" zeroCouponBond
         <> multilineString "couponBondGuaranteed" couponBondGuaranteed
         <> multilineString "swap" swap
        haskellUsecasesModule = psModule "Examples.Haskell.Contracts" haskellUsecases
    createDirectoryIfMissing True (outputDir </> "Examples" </> "Haskell")
    BS.writeFile (outputDir </> "Examples" </> "Haskell" </> "Contracts.purs") haskellUsecasesModule
    let contractToString = BS8.pack . show . pretty
        marloweUsecases =
            multilineString "escrow" (contractToString Escrow.contract)
         <> multilineString "zeroCouponBond" (contractToString ZeroCouponBond.contract)
         <> multilineString "option" (contractToString Option.contract)
         <> multilineString "swap" (contractToString Swap.contract)
        marloweUsecasesModule = psModule "Examples.Marlowe.Contracts" marloweUsecases
    createDirectoryIfMissing True (outputDir </> "Examples" </> "Marlowe")
    BS.writeFile (outputDir </> "Examples" </> "Marlowe" </> "Contracts.purs") marloweUsecasesModule
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
