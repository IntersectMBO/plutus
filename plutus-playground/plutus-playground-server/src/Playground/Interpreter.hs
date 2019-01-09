{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Playground.Interpreter where

import           Control.Monad                (unless)
import           Control.Monad.Catch          (finally, throwM)
import           Control.Monad.Error.Class    (MonadError, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import qualified Control.Newtype.Generics     as Newtype
import           Data.Aeson                   (ToJSON, encode)
import qualified Data.Aeson                   as JSON
import qualified Data.ByteString              as BS
import qualified Data.ByteString.Char8        as BSC
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.FileEmbed               (embedFile)
import           Data.List                    (intercalate)
import           Data.Maybe                   (catMaybes)
import           Data.Monoid                  ((<>))
import           Data.Swagger                 (Schema)
import qualified Data.Text                    as Text
import qualified Data.Text.Internal.Search    as Text
import           Language.Haskell.Interpreter (Extension (..), GhcError (GhcError),
                                               InterpreterError (UnknownError, WontCompile), ModuleElem (Fun),
                                               ModuleName, MonadInterpreter, OptionVal ((:=)), as, getLoadedModules,
                                               getModuleExports, interpret, languageExtensions, loadModules, set,
                                               setImportsQ, setTopLevelModules, typeOf)
import           Ledger.Types                 (Blockchain, Value)
import           Playground.API               (Evaluation (program, sourceCode), Expression (Action, Wait), Fn (Fn),
                                               FunctionSchema,
                                               PlaygroundError (DecodeJsonTypeError, FunctionSchemaError, InterpreterError),
                                               SourceCode (SourceCode), wallets)
import           Playground.Contract          (payToPublicKey_)
import qualified Playground.TH                as TH
import           Playground.Usecases          (vesting)
import           System.Directory             (removeFile)
import           System.IO.Temp               (writeSystemTempFile)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet)

$(TH.mkFunction 'payToPublicKey_)

defaultExtensions :: [Extension]
defaultExtensions =
    [ DataKinds
    , DeriveAnyClass
    , DeriveFoldable
    , DeriveFunctor
    , DeriveGeneric
    , DeriveLift
    , DeriveTraversable
    , ExplicitForAll
    , FlexibleContexts
    , OverloadedStrings
    , RecordWildCards
    , ScopedTypeVariables
    , StandaloneDeriving
    , TemplateHaskell
    ]

loadSource :: (MonadInterpreter m) => FilePath -> (ModuleName -> m a) -> m a
loadSource fileName action =
    flip finally (liftIO (removeFile fileName)) $ do
        set [languageExtensions := defaultExtensions]
        loadModules [fileName]
        (m:_) <- getLoadedModules
        setTopLevelModules [m]
        action m

avoidUnsafe :: (MonadError PlaygroundError m) => SourceCode -> m ()
avoidUnsafe s =
    unless (null . Text.indices "unsafe" . Newtype.unpack $ s) $
    throwError
        (InterpreterError
             (WontCompile [GhcError "Cannot interpret unsafe functions"]))

addGhcOptions :: SourceCode -> SourceCode
addGhcOptions = Newtype.over SourceCode (mappend opts)
  where
    opts =
        "{-# OPTIONS_GHC -O0 #-}\n"

writeTempSource :: MonadIO m => SourceCode -> m FilePath
writeTempSource s =
    liftIO $
    writeSystemTempFile
        "Contract.hs"
        (Text.unpack . Newtype.unpack . addGhcOptions $ s)

warmup ::
       (MonadInterpreter m, MonadError PlaygroundError m)
    => m [FunctionSchema Schema]
warmup = compile . SourceCode . Text.pack . BSC.unpack $ vesting

compile ::
       (MonadInterpreter m, MonadError PlaygroundError m)
    => SourceCode
    -> m [FunctionSchema Schema]
compile s = do
    avoidUnsafe s
    fileName <- writeTempSource s
    loadSource fileName $ \moduleName -> do
        exports <- getModuleExports moduleName
        walletFunctions <- catMaybes <$> traverse isWalletFunction exports
        schemas <- traverse getSchema walletFunctions
        pure (schemas <> pure payToPublicKey_Schema)

jsonToString :: ToJSON a => a -> String
jsonToString = show . JSON.encode

{-# ANN getSchema ("HLint: ignore" :: String) #-}

getSchema ::
       (MonadInterpreter m, MonadError PlaygroundError m)
    => ModuleElem
    -> m (FunctionSchema Schema)
getSchema (Fun m) = interpret m (as :: FunctionSchema Schema)
getSchema _       = throwError FunctionSchemaError
  -- error "Trying to get a schema by calling something other than a function"

{-# ANN getJsonString ("HLint: ignore" :: String) #-}

getJsonString :: (MonadError PlaygroundError m) => JSON.Value -> m String
getJsonString (JSON.String s) = pure $ Text.unpack s
getJsonString v =
    throwError . DecodeJsonTypeError "String" . BSL.unpack . encode $ v

runFunction ::
       (MonadInterpreter m, MonadError PlaygroundError m)
    => Evaluation
    -> m (Blockchain, [EmulatorEvent], [(Wallet, Value)])
runFunction evaluation = do
    avoidUnsafe $ sourceCode evaluation
    expr <- mkExpr evaluation
    fileName <- writeTempSource $ sourceCode evaluation
    loadSource fileName $ \_ -> do
        setImportsQ
            [ ("Playground.Interpreter.Util", Nothing)
            , ("Playground.API", Nothing)
            , ("Wallet.Emulator", Nothing)
            , ("Ledger.Types", Nothing)
            , ("Data.Map", Nothing)
            ]
        liftIO . putStrLn $ expr
        res <-
            interpret
                expr
                (as :: Either PlaygroundError ( Blockchain
                                              , [EmulatorEvent]
                                              , [(Wallet, Value)]))
        case res of
            Left e  -> throwM . UnknownError $ show e
            Right r -> pure r

mkExpr :: (MonadError PlaygroundError m) => Evaluation -> m String
mkExpr evaluation = do
    let allWallets = fst <$> wallets evaluation
    exprs <- traverse (walletActionExpr allWallets) (program evaluation)
    pure $
        "runTrace (decode' " <> jsonToString (wallets evaluation) <> ") [" <>
        intercalate ", " exprs <>
        "]"

walletActionExpr ::
       (MonadError PlaygroundError m) => [Wallet] -> Expression -> m String
walletActionExpr allWallets (Action (Fn f) wallet args) = do
    argStrings <- fmap show <$> traverse getJsonString args
    pure $
        "(runWalletActionAndProcessPending (" <> show allWallets <> ") (" <>
        show wallet <>
        ") <$> (" <>
        mkApplyExpr (Text.unpack f) argStrings <>
        "))"
-- We return an empty list to fix types as wallets have already been notified
walletActionExpr allWallets (Wait blocks) =
    pure $
    "pure $ addBlocksAndNotify (" <> show allWallets <> ") " <> show blocks <>
    " >> pure []"

mkApplyExpr :: String -> [String] -> String
mkApplyExpr functionName [] = "apply" <+> functionName
mkApplyExpr functionName [a] = "apply1" <+> functionName <+> a
mkApplyExpr functionName [a, b] = "apply2" <+> functionName <+> a <+> b
mkApplyExpr functionName [a, b, c] = "apply3" <+> functionName <+> a <+> b <+> c
mkApplyExpr functionName [a, b, c, d] =
    "apply4" <+> functionName <+> a <+> b <+> c <+> d
mkApplyExpr functionName [a, b, c, d, e] =
    "apply5" <+> functionName <+> a <+> b <+> c <+> d <+> e
mkApplyExpr functionName [a, b, c, d, e, f] =
    "apply6" <+> functionName <+> a <+> b <+> c <+> d <+> e <+> f
mkApplyExpr functionName [a, b, c, d, e, f, g] =
    "apply7" <+> functionName <+> a <+> b <+> c <+> d <+> e <+> f <+> g

(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

isWalletFunction :: (MonadInterpreter m) => ModuleElem -> m (Maybe ModuleElem)
isWalletFunction f@(Fun s) = do
    t <- typeOf s
    liftIO . putStrLn $ "COMPILED: " <> s <> " :: " <> t
    pure $
        if t == "FunctionSchema Schema" ||
           t == "Playground.API.FunctionSchema Data.Swagger.Internal.Schema" ||
           t == "Playground.API.FunctionSchema a" || t == "FunctionSchema a"
            then Just f
            else Nothing
isWalletFunction _ = pure Nothing
