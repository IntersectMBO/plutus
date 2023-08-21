{-# LANGUAGE OverloadedStrings #-}

{- | This executable is for
(1) easy addition/updates of tests of a chosen directory.
One can also use the golden test accept option to update all tests in a test suite.
(2) debugging failed Agda UPLC evaluator tests of a chosen directory.
-}
module Main (
    main,
) where

import Control.Monad.Trans.Except
import Data.Foldable (for_)
import Data.Text.IO qualified as T
import MAlonzo.Code.Main (runUAgda)
import Options.Applicative
import Options.Applicative.Help.Pretty (Doc, string)
import PlutusConformance.Common
import PlutusCore.Error (Error (..), ParserErrorBundle (ParseErrorB))
import PlutusCore.Pretty (Pretty (pretty), Render (render))
import PlutusCore.Quote (Quote, runQuote)
import Test.Tasty.Golden (findByExtension)
import UntypedPlutusCore (DefaultFun, DefaultUni)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn

-- |  The arguments to the executable.
data Args = MkArgs
    { _argExt     :: String
    -- ^ file extension to be searched
    , _argDir     :: FilePath
    -- ^ directory to be searched
    -- | the action to run the input files through;
    -- eval (for updating evaluation tests)
    -- or typecheck (for updating typechecking tests)
    -- or debug (for debugging the Agda UPLC evaluator)
    , _argFeature :: Feature
    }

ext :: Parser String
ext =
    strArgument
        ( metavar "EXT"
            <> help "The input file(s) with this extension will be included."
        )

dir :: Parser FilePath
dir =
    strArgument
        (metavar "DIR" <> help "The directory the input files are in.")

data Feature
    = GenTestOutput Runner
    | Debug

feature :: Parser Feature
feature =
    argument
        (eitherReader featureReader)
        ( metavar "FEATURE"
            <> help
                ( "The feature you want: Either \"eval\" or \"typecheck\" to generate test outputs,"
                    <> " or \"debug\" for debugging the Agda UPLC evaluator."
                )
        )

featureReader :: String -> Either String Feature
featureReader "eval" = Right $ GenTestOutput Eval
featureReader "typecheck" = Right $ GenTestOutput Typecheck
-- currently we can only debug the agda implementation, may add others later
featureReader "debug" = Right Debug
featureReader inp =
    Left
        ( "Unsupported feature "
            <> show inp
            <> ". Please choose either eval (for generating evaluation test outputs), "
            <> "or typecheck (for generating typechecking test outputs), "
            <> "or debug (for debugging failed tests)."
        )

data Runner
    = Eval
    | Typecheck
    deriving stock (Show)

args :: ParserInfo Args
args =
    info
        ((MkArgs <$> ext <*> dir <*> feature) <**> helper)
        -- using progDescDoc instead of progDesc because progDesc messes up the formatting.
        (fullDesc <> progDescDoc (Just helpText))

helpText :: Doc
helpText =
    string $
        unlines
            [ "This program adds test outputs to specified inputs."
            , "To run the program, input the following 3 arguments:"
            , "(1) file extension to be searched"
            , "(2) directory to be searched"
            , "(3) the action to run the input files through;"
            , "eval (for evaluation tests),"
            , "or typecheck (for typechecking tests),"
            , "or debug (for debugging failed tests)."
            , "E.g. run \n"
            , "`cabal run test-utils .uplc plutus-conformance/test-cases/uplc/ eval`\n"
            , "to have the executable search for files with extension `.uplc`"
            , "in the /uplc directory."
            , "It will evaluate and create output files for them."
            ]

main :: IO ()
main = do
    MkArgs extension directory run <- customExecParser (prefs showHelpOnEmpty) args
    -- the files of the directory chosen by the user
    inputFiles <- findByExtension [extension] directory
    for_ inputFiles $ \inputFile -> do
        inputTxt <- T.readFile inputFile
        let parsed = parseTxt inputTxt
            outFilePath = inputFile <> ".expected"
        case parsed of
            Left (ParseErrorB _) ->
                case run of
                    GenTestOutput Eval ->
                        do
                            -- specifying parsed to ParserError for the compiler
                            -- warn the user that the file failed to parse
                            putStrLn $
                                inputFile <> " failed to parse. Error written to " <> outFilePath
                            T.writeFile outFilePath shownParseError
                    _ -> pure () -- for debug mode we don't want to see the failed to parse cases.
            Right pro -> do
                case run of
                    GenTestOutput Eval ->
                        case evalUplcProg (() <$ pro) of
                            (Just prog) -> do
                                T.writeFile outFilePath (render $ pretty prog)
                                putStrLn $
                                    inputFile <> " evaluated; result written to " <> outFilePath
                            Nothing -> do
                                -- warn the user that the file failed to evaluate
                                T.writeFile outFilePath shownEvaluationFailure
                                putStrLn $
                                    inputFile
                                        <> " failed to evaluate. Failure written to "
                                        <> outFilePath
                    GenTestOutput Typecheck ->
                        putStrLn $
                            "typechecking has not been implemented yet."
                                <> "Only evaluation tests (eval) "
                                <> "or debugging (debug) are supported."
                    Debug ->
                        case agdaEvalUplcProgDebug (() <$ pro) of
                            (Right _prog) -> pure ()
                            (Left err) ->
                                -- warn the user that the file failed to evaluate
                                putStrLn $ inputFile <> " failed to evaluate. " <> err

-- | For debugging failed UPLC evaluation tests (Agda implementation). Called by `test-utils`.
agdaEvalUplcProgDebug :: UplcProg -> Either String UplcProg
agdaEvalUplcProgDebug (UPLC.Program () version tmU) =
    let
        -- turn it into an untyped de Bruijn term
        tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
        tmUDB = deBruijnTerm tmU
    in
    case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
        -- if there's an exception, evaluation failed, should return `Nothing`.
        Left fvError ->
            Left $ "deBruijnTerm returned an error: "
                <> show (fvError :: Error DefaultUni DefaultFun ())
        -- evaluate the untyped term with CEK
        Right tmUDBSuccess ->
            case runUAgda tmUDBSuccess of
                Left evalError ->
                    Left $ "runUAgda returned an error: " <> show evalError <>
                        "The input to runUAgda was " <> show tmUDBSuccess <>
                        ", returned by deBruijnTerm."
                Right tmEvaluated ->
                    let tmNamed = runQuote $ runExceptT $
                            withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated
                    in
                    -- turn it back into a named term
                    case tmNamed of
                        Left (err :: Error DefaultUni DefaultFun ())          ->
                            Left $
                                "unDeBruijnTerm returned an error: " <> show err <>
                                "The input to unDebruijnTerm was " <> show tmEvaluated <>
                                ", returned by runUAgda." <>
                                "The input to runUAgda was " <> show tmUDBSuccess <>
                                ", returned by deBruijnTerm."
                        Right namedTerm -> Right $ UPLC.Program () version namedTerm
