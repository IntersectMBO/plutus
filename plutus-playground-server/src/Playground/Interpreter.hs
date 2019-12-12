{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Playground.Interpreter where

import           Control.Exception            (IOException, try)
import           Control.Monad.Catch          (MonadMask)
import           Control.Monad.Error.Class    (MonadError, liftEither, throwError)
import           Control.Monad.Except.Extras  (mapError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import qualified Control.Newtype.Generics     as Newtype
import qualified Data.Aeson                   as JSON
import           Data.Bifunctor               (first)
import qualified Data.ByteString.Char8        as BS8
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.IO                 as Text
import           Data.Time.Units              (Second, TimeUnit)
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError),
                                               InterpreterError (CompilationErrors),
                                               InterpreterResult (InterpreterResult), SourceCode (SourceCode),
                                               Warning (Warning), avoidUnsafe, runghc)
import           Language.Haskell.TH          (Ppr, Q, pprint, runQ)
import           Language.Haskell.TH.Syntax   (liftString)
import           Playground.Types             (CompilationResult (CompilationResult),
                                               Evaluation (program, sourceCode, wallets), EvaluationResult,
                                               PlaygroundError (InterpreterError, JsonDecodingError, OtherError, decodingError, expected, input))
import           System.FilePath              ((</>))
import           System.IO                    (Handle, IOMode (ReadWriteMode), hFlush)
import           System.IO.Extras             (withFile)
import           System.IO.Temp               (withSystemTempDirectory)
import qualified Text.Regex                   as Regex


maxInterpretationTime :: Second
maxInterpretationTime = 80

replaceModuleName :: Text -> Text
replaceModuleName script =
    let scriptString = Text.unpack script
        regex = Regex.mkRegex "module .* where"
     in Text.pack $ Regex.subRegex regex scriptString "module Main where"

ensureMinimumImports :: (MonadError InterpreterError m) => SourceCode -> m ()
ensureMinimumImports script =
    let scriptString = Text.unpack . Newtype.unpack $ script
        regex =
            Regex.mkRegex
                "^import[ \t]+Playground.Contract([ ]*$|[ \t]+\\(.*printSchemas.*\\)|[ \t]+\\(.*printSchemas.*\\))"
        mMatches = Regex.matchRegexAll regex scriptString
     in case mMatches of
            Just _ -> pure ()
            Nothing ->
                let filename = ""
                    row = 1
                    column = 1
                    text =
                        [ "You need to import `printSchemas` in order to compile successfully, you can do this with either"
                        , "`import Playground.Contract`"
                        , "or"
                        , "`import Playground.Contract (printSchemas)`"
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
    replaceModuleName script <>
    Text.unlines
        [ ""
        , "$ensureIotsDefinitions"
        , "$ensureKnownCurrencies"
        , ""
        , "main :: IO ()"
        , "main = printSchemas (schemas, registeredKnownCurrencies, iotsDefinitions)"
        ]

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
    withSystemTempDirectory "playgroundcompile" $ \dir -> do
        let file = dir </> "Main.hs"
        withFile file ReadWriteMode $ \handle -> do
            (InterpreterResult warnings result) <-
                runscript handle file timeout . mkCompileScript . Newtype.unpack $
                source
            let eSchema = JSON.eitherDecodeStrict . BS8.pack $ result
            case eSchema of
                Left err ->
                    throwError . CompilationErrors . pure . RawError $
                    "unable to decode compilation result: " <> Text.pack err <>
                    "\n" <>
                    Text.pack result
                Right ([schema], currencies, iots) -> do
                    let warnings' =
                            Warning
                                "It looks like you have not made any functions available, use `$(mkFunctions ['functionA, 'functionB])` to be able to use `functionA` and `functionB`" :
                            warnings
                    pure . InterpreterResult warnings' $
                        CompilationResult [schema] currencies iots
                Right (schemas, currencies, iots) ->
                    pure . InterpreterResult warnings $
                    CompilationResult schemas currencies iots

evaluateSimulation ::
       ( Show t
       , TimeUnit t
       , MonadMask m
       , MonadIO m
       , MonadError PlaygroundError m
       )
    => t
    -> Evaluation
    -> m (InterpreterResult EvaluationResult)
evaluateSimulation timeout evaluation = do
    let source = sourceCode evaluation
    mapError InterpreterError $ avoidUnsafe source
    expr <- mkExpr evaluation
    withSystemTempDirectory "playgroundrun" $ \dir -> do
        let file = dir </> "Main.hs"
        withFile file ReadWriteMode $ \handle -> do
            (InterpreterResult warnings result) <-
                mapError InterpreterError . runscript handle file timeout $
                mkRunScript source (Text.pack expr)
            let decodeResult =
                    JSON.eitherDecodeStrict . BS8.pack $ result :: Either String (Either PlaygroundError EvaluationResult)
            case decodeResult of
                Left err ->
                    throwError
                        JsonDecodingError
                            { expected = "TraceResult"
                            , decodingError = err
                            , input = result
                            }
                Right eResult ->
                    case eResult of
                        Left err -> throwError err
                        Right result' ->
                            pure $ InterpreterResult warnings result'

mkRunScript :: SourceCode -> Text -> Text
mkRunScript (SourceCode script) expr =
    replaceModuleName script <> "\n\nmain :: IO ()" <> "\nmain = printJson $ " <>
    expr

runghcOpts :: [String]
runghcOpts =
    [ "-XDataKinds"
    , "-XDeriveAnyClass"
    , "-XDeriveGeneric"
    , "-XDerivingStrategies"
    , "-XExplicitNamespaces"
    , "-XFlexibleContexts"
    , "-XGeneralizedNewtypeDeriving"
    , "-XNamedFieldPuns"
    , "-XNoImplicitPrelude"
    , "-XOverloadedStrings"
    , "-XRecordWildCards"
    , "-XScopedTypeVariables"
    , "-XTemplateHaskell"
    , "-XTypeApplications"
    , "-XTypeFamilies"
    , "-XTypeOperators"
    -- See Plutus Tx readme
    -- runghc is interpreting our code
    , "-fno-ignore-interface-pragmas"
    , "-fobject-code"
    -- FIXME: stupid GHC bug still
    , "-package plutus-tx"
    , "-package plutus-wallet-api"
    ]

mkExpr :: (MonadError PlaygroundError m, MonadIO m) => Evaluation -> m String
mkExpr evaluation = do
    let programJson = liftString . BSL.unpack . JSON.encode $ program evaluation
        simulatorWalletsJson =
            liftString . BSL.unpack . JSON.encode $ wallets evaluation
    printQ [|stage endpoints $(programJson) $(simulatorWalletsJson)|]

printQ :: (MonadError PlaygroundError m, MonadIO m, Ppr a) => Q a -> m String
printQ q = do
    str <- liftIO . fmap toPlaygroundError . try . runQ . fmap pprint $ q
    liftEither str
  where
    toPlaygroundError :: Either IOException a -> Either PlaygroundError a
    toPlaygroundError = first (OtherError . show)

{-# ANN getJsonString ("HLint: ignore" :: String) #-}

getJsonString :: (MonadError PlaygroundError m) => JSON.Value -> m String
getJsonString (JSON.String s) = pure $ Text.unpack s
getJsonString v =
    throwError
        JsonDecodingError
            { expected = "String"
            , input = BSL.unpack $ JSON.encode v
            , decodingError = "Expected a String."
            }
