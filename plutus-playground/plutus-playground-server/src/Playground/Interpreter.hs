{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Playground.Interpreter where

import           Control.Monad                (unless)
import           Control.Monad.Catch          (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Error.Class    (MonadError, throwError)
import           Control.Monad.Except.Extras  (mapError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import qualified Control.Newtype.Generics     as Newtype
import           Data.Aeson                   (ToJSON)
import qualified Data.Aeson                   as JSON
import           Data.ByteString              (ByteString)
import qualified Data.ByteString.Char8        as BS8
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.List                    (intercalate)
import           Data.Swagger                 (Schema)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.Internal.Search    as Text
import qualified Data.Text.IO                 as Text
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError), runghc)
import           Ledger.Ada                   (Ada)
import           Ledger.Types                 (Blockchain, Value)
import           Playground.API               (CompilationResult (CompilationResult), Evaluation (sourceCode),
                                               Expression (Action, Wait), Fn (Fn),
                                               PlaygroundError (CompilationErrors, DecodeJsonTypeError, InterpreterError, OtherError),
                                               SimulatorWallet, SourceCode, Warning (Warning), parseErrorsText, program,
                                               simulatorWalletWallet, toSimpleArgumentSchema, wallets)
import           System.Directory             (removeFile)
import           System.Environment           (lookupEnv)
import           System.Exit                  (ExitCode (ExitSuccess))
import           System.IO                    (Handle, hClose, hFlush)
import           System.IO.Temp.Extras        (withSystemTempFile)
import           System.Process               (readProcessWithExitCode)
import qualified Text.Regex                   as Regex
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet)

replaceModuleName :: Text -> Text
replaceModuleName script =
    let scriptString = Text.unpack script
        regex = Regex.mkRegex "module .* where"
     in Text.pack $ Regex.subRegex regex scriptString "module Main where"

ensureMkFunctionExists :: Text -> Text
ensureMkFunctionExists script =
    let scriptString = Text.unpack script
        regex = Regex.mkRegex "^\\$\\(mkFunctions \\[.*])"
        mMatches = Regex.matchRegexAll regex scriptString
     in case mMatches of
            Nothing -> script <> "\n$(mkFunctions [])"
            Just _  -> script

mkCompileScript :: Text -> Text
mkCompileScript script =
    (ensureMkFunctionExists . replaceModuleName) script <> "\n\nmain :: IO ()" <>
    "\nmain = printSchemas schemas"

avoidUnsafe :: (MonadError PlaygroundError m) => SourceCode -> m ()
avoidUnsafe s =
    unless (null . Text.indices "unsafe" . Newtype.unpack $ s) $
    throwError $ OtherError "Cannot interpret unsafe functions"

runscript
    :: (MonadMask m, MonadIO m, MonadError [CompilationError] m)
    => Handle
    -> FilePath
    -> Text
    -> m String
runscript handle file script = do
    liftIO $ Text.hPutStr handle script
    liftIO $ hFlush handle
    runghc runghcOpts file

compile ::
       (MonadMask m, MonadIO m, MonadError PlaygroundError m)
    => SourceCode
    -> m CompilationResult
compile source = do
    avoidUnsafe source
    withSystemTempFile "Main.hs" $ \file handle -> do
        result <-
            mapError CompilationErrors . runscript handle file . mkCompileScript . Newtype.unpack $ source
        let eSchema = JSON.eitherDecodeStrict . BS8.pack $ result
        case eSchema of
            Left err ->
                throwError . OtherError $
                "unable to decode compilation result" <> err
            Right [schema] ->
                pure . CompilationResult [toSimpleArgumentSchema <$> schema] $
                [ Warning
                      "It looks like you have not made any functions available, use `$(mkFunctions ['functionA, 'functionB])` to be able to use `functionA` and `functionB`"
                ]
            Right schemas ->
                pure $
                CompilationResult (fmap toSimpleArgumentSchema <$> schemas) []

runFunction ::
       (MonadMask m, MonadIO m, MonadError PlaygroundError m)
    => Evaluation
    -> m (Blockchain, [EmulatorEvent], [SimulatorWallet])
runFunction evaluation = do
    let source = sourceCode evaluation
    avoidUnsafe source
    expr <- mkExpr evaluation
    withSystemTempFile "Main.hs" $ \file handle -> do
        result <-
            mapError CompilationErrors .
            runscript handle file $
            mkRunScript (Newtype.unpack source) (Text.pack . BS8.unpack $ expr)
        let decodeResult =
                JSON.eitherDecodeStrict . BS8.pack $ result :: Either String (Either PlaygroundError ( Blockchain
                                                                                                     , [EmulatorEvent]
                                                                                                     , [SimulatorWallet]))
        case decodeResult of
            Left err ->
                throwError . OtherError $
                "unable to decode compilation result" <> err
            Right eResult ->
                case eResult of
                    Left err      -> throwError err
                    Right result' -> pure result'

mkRunScript :: Text -> Text -> Text
mkRunScript script expr =
    replaceModuleName script <> "\n\nmain :: IO ()" <> "\nmain = printJson $ " <>
    expr

runghcOpts :: [String]
runghcOpts =
    [ "-XDataKinds"
    , "-XDeriveAnyClass"
    , "-XDeriveFoldable"
    , "-XDeriveFunctor"
    , "-XDeriveGeneric"
    , "-XDeriveLift"
    , "-XDeriveTraversable"
    , "-XExplicitForAll"
    , "-XFlexibleContexts"
    , "-XOverloadedStrings"
    , "-XRecordWildCards"
    , "-XStandaloneDeriving"
    , "-XTemplateHaskell"
    , "-XScopedTypeVariables"
    , "-O0"
    -- FIXME: workaround for https://ghc.haskell.org/trac/ghc/ticket/16228
    -- This appears to sometimes be necessary and sometimes not be, depending
    -- on apparently unrelated changes in the packages this depends on. I'm
    -- blaming the GHC bug.
    , "-package plutus-tx"
    ]

jsonToString :: ToJSON a => a -> String
jsonToString = show . JSON.encode

mkExpr :: (MonadError PlaygroundError m) => Evaluation -> m ByteString
mkExpr evaluation = do
    let allWallets = simulatorWalletWallet <$> wallets evaluation
    exprs <- traverse (walletActionExpr allWallets) (program evaluation)
    pure . BS8.pack $
        "runTrace (decode' " <> jsonToString (wallets evaluation) <> ") [" <>
        intercalate ", " exprs <>
        "]"

{-# ANN getJsonString ("HLint: ignore" :: String) #-}

getJsonString :: (MonadError PlaygroundError m) => JSON.Value -> m String
getJsonString (JSON.String s) = pure $ Text.unpack s
getJsonString v =
    throwError . DecodeJsonTypeError "String" . BSL.unpack . JSON.encode $ v

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

{-# ANN mkApplyExpr ("HLint: ignore" :: String) #-}

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
mkApplyExpr _ _ = error "cannot apply more than 7 arguments"

(<+>) :: String -> String -> String
a <+> b = a <> " " <> b
