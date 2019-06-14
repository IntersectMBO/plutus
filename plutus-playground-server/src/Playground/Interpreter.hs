{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Playground.Interpreter where

import           Control.Monad.Catch          (MonadMask)
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
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.IO                 as Text
import           Data.Time.Units              (TimeUnit)
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError),
                                               InterpreterError (CompilationErrors),
                                               InterpreterResult (InterpreterResult), SourceCode, Warning (Warning),
                                               avoidUnsafe, runghc)
import           Playground.API               (CompilationResult (CompilationResult), Evaluation (sourceCode),
                                               Expression (Action, Wait), Fn (Fn),
                                               PlaygroundError (DecodeJsonTypeError, OtherError), program,
                                               simulatorWalletWallet, wallets)
import qualified Playground.API               as API
import           Playground.Interpreter.Util  (TraceResult)
import           System.IO                    (Handle, hFlush)
import           System.IO.Temp.Extras        (withSystemTempFile)
import qualified Text.Regex                   as Regex
import           Wallet.Emulator.Types        (Wallet)

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

ensureMinimumImports :: (MonadError InterpreterError m) => SourceCode -> m ()
ensureMinimumImports script =
    let scriptString = Text.unpack . Newtype.unpack $ script
        regex =
            Regex.mkRegex
                "^import[ \t]+Playground.Contract([ ]*$|[ \t]+\\(.*mkFunctions.*printSchema.*\\)|[ \t]+\\(.*printSchema.*mkFunctions.*\\))"
        mMatches = Regex.matchRegexAll regex scriptString
     in case mMatches of
            Just _ -> pure ()
            Nothing ->
                let filename = ""
                    row = 1
                    column = 1
                    text =
                        [ "You need to import the `mkFunctions` and `printSchema` in order to compile successfully, you can do this with either"
                        , "`import Playground.Contract`"
                        , "or"
                        , "`import Playground.Contract (mkFunctions, printSchema)`"
                        ]
                    errors = [CompilationError filename row column text]
                 in throwError $ CompilationErrors errors

ensureKnownCurrenciesExists :: Text -> Text
ensureKnownCurrenciesExists script =
    let scriptString = Text.unpack script
        regex = Regex.mkRegex "^\\$\\(mkKnownCurrencies \\[.*])"
        mMatches = Regex.matchRegexAll regex scriptString
     in case mMatches of
            Nothing -> script <> "\n$(mkKnownCurrencies [])"
            Just _  -> script

mkCompileScript :: Text -> Text
mkCompileScript script =
    (ensureKnownCurrenciesExists . ensureMkFunctionExists . replaceModuleName)
        script <>
    "\n\nmain :: IO ()" <>
    "\nmain = printSchema (schema, registeredKnownCurrencies)"

runscript ::
       ( Show t
       , TimeUnit t
       , MonadMask m
       , MonadIO m
       , MonadError InterpreterError m
       )
    => Handle
    -> FilePath
    -> t
    -> Text
    -> m (InterpreterResult String)
runscript handle file timeout script = do
    liftIO $ Text.hPutStr handle script
    liftIO $ hFlush handle
    runghc timeout runghcOpts file

compile ::
       ( Show t
       , TimeUnit t
       , MonadMask m
       , MonadIO m
       , MonadError InterpreterError m
       )
    => t
    -> SourceCode
    -> m (InterpreterResult CompilationResult)
compile timeout source
    -- There are a couple of custom rules required for compilation
 = do
    avoidUnsafe source
    ensureMinimumImports source
    withSystemTempFile "Main.hs" $ \file handle -> do
        (InterpreterResult warnings result) <-
            runscript handle file timeout . mkCompileScript . Newtype.unpack $
            source
        let eSchema = JSON.eitherDecodeStrict . BS8.pack $ result
        case eSchema of
            Left err ->
                throwError . CompilationErrors . pure . RawError $
                "unable to decode compilation result" <> Text.pack err
            Right (schema, currencies) -> do
                let warnings' =
                        Warning
                            "It looks like you have not made any functions available, use `$(mkFunctions ['functionA, 'functionB])` to be able to use `functionA` and `functionB`" :
                        warnings
                pure . InterpreterResult warnings' $
                    CompilationResult schema currencies
            Right (schemas, currencies) ->
                pure . InterpreterResult warnings $
                CompilationResult schemas currencies

runFunction ::
       ( Show t
       , TimeUnit t
       , MonadMask m
       , MonadIO m
       , MonadError PlaygroundError m
       )
    => t
    -> Evaluation
    -> m (InterpreterResult TraceResult)
runFunction timeout evaluation = do
    let source = sourceCode evaluation
    mapError API.InterpreterError $ avoidUnsafe source
    expr <- mkExpr evaluation
    withSystemTempFile "Main.hs" $ \file handle -> do
        (InterpreterResult warnings result) <-
            mapError API.InterpreterError . runscript handle file timeout $
            mkRunScript (Newtype.unpack source) (Text.pack . BS8.unpack $ expr)
        let decodeResult =
                JSON.eitherDecodeStrict . BS8.pack $ result :: Either String (Either PlaygroundError TraceResult)
        case decodeResult of
            Left err ->
                throwError . OtherError $
                "unable to decode compilation result" <> err
            Right eResult ->
                case eResult of
                    Left err      -> throwError err
                    Right result' -> pure $ InterpreterResult warnings result'

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
    , "-XKindSignatures"
    , "-XRecordWildCards"
    , "-XStandaloneDeriving"
    , "-XTemplateHaskell"
    , "-XScopedTypeVariables"
    , "-XNoImplicitPrelude"
    -- See Plutus Tx readme
    -- runghc is interpreting our code
    , "-fno-ignore-interface-pragmas"
    , "-fobject-code"
    -- FIXME: stupid GHC bug still
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
