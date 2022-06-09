{-# LANGUAGE OverloadedStrings #-}

{- | This executable is for easy addition of tests. When run with the option `-- --missing`,
output files will be added to all tests that had no output files.
You can specify to add outputs to all input files with `-- --all`.
You are advised to manually check that the outputs are correct.
In other parts of the codebase we use golden tests with the `accept` test option turned on.
Here we use an executable for easier customization.
 -}

module Main
    ( main
    ) where

import Common
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (filterM)
import Data.Foldable (for_)
import Data.Text.IO qualified as T
import Options.Applicative
import PlutusCore.Error (ParserErrorBundle (ParseErrorB))
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.Pretty (Pretty (pretty), Render (render))
import System.Directory (doesFileExist)
import Test.Tasty.Golden (findByExtension)

-- |  The arguments to the executable.
data Args = MkArgs
  { _argExt       :: String -- ^ file extension to be searched
  , _argDir       :: FilePath -- ^ directory to be searched
  , _argRunner    :: Runner
  -- ^ the action to run the input files through; eval (for evaluation tests) or typecheck (for typechecking tests)
  , _allOrMissing :: SomeOrAll -- ^ whether to write all output files or only the ones with missing outputs.
  }

ext :: Parser String
ext =
  strArgument
  (metavar "EXT" <>
    help "The input file(s) with this extension will be included." )

dir :: Parser FilePath
dir =
  strArgument
    (metavar "DIR" <> help "The directory the input files are in." )

data Runner =
  Eval
  | Typecheck
  deriving stock (Show)

runner :: Parser Runner
runner = argument
  (eitherReader runnerReader)
  (metavar "RUNNER" <> help "The action to apply to the input files that generate the outputs. Either eval or typecheck." )

runnerReader :: String -> Either String Runner
runnerReader "eval" = Right Eval
runnerReader "typecheck" = Right Typecheck
runnerReader inp =
  Left ("Unsupported test " <> show inp <>
        ". Please choose either eval (for evaluation tests) or typecheck (for typechecking tests).")

data SomeOrAll =
  Missing
  | All

missing :: Parser SomeOrAll
missing =
  flag' Missing ( long "missing"
    <> short 'm'
    <> help "only add missing outputs" )

allInputs :: Parser SomeOrAll
allInputs =
  flag' All ( long "all"
    <> short 'a'
    <> help "add outputs to all input files" )

allOrMissing :: Parser SomeOrAll
allOrMissing = missing <|> allInputs

args :: ParserInfo Args
args = info ((MkArgs <$> ext <*> dir <*> runner <*> allOrMissing) <**> helper)
  (fullDesc <> progDesc helpText)

helpText :: String
helpText = unlines
  ["This program adds test outputs to specified inputs."
  , "To run the program, input the following 4 arguments: "
  , "(1) file extension to be searched "
  , "(2) directory to be searched "
  , "(3) the action to run the input files through; eval (for evaluation tests) or typecheck (for typechecking tests). "
  , "(4) whether to write output files to all inputs or only the ones missing output files."
  , "E.g. run "
  , "`cabal run add-test-output .uplc plutus-conformance/uplc/ eval` -- --missing"
  , "to have the executable search for files with extension `.uplc` in the /uplc directory that are missing output files. "
  , " It will evaluate and create output files for them."
  ]

main :: IO ()
main = do
    MkArgs extension directory run fileOpt <- customExecParser (prefs showHelpOnEmpty) args
    allInputFiles <- findByExtension [extension] directory
    inputFiles <-
      case fileOpt of
        Missing -> filterM (fmap (fmap not) (\testIn -> doesFileExist (testIn <> ".expected"))) allInputFiles
        All     -> pure allInputFiles
    case run of
      Eval ->
        for_ inputFiles printAndWrite
          where printAndWrite inputFile = do
                  inputTxt <- T.readFile inputFile
                  let parsed = parseTxt inputTxt
                      outFilePath = inputFile <> ".expected"
                  case parsed of
                    Left (ParseErrorB _) -> do -- specifying parsed to ParserError for the compiler
                      -- warn the user that the file failed to parse
                      putStrLn $ inputFile <> " failed to parse. Error written to " <> outFilePath
                      T.writeFile outFilePath shownParseError
                    Right pro -> do
                      res <- try (evaluate $ evalUplcProg (() <$ pro)):: IO (Either SomeException (EvaluationResult UplcProg))
                      case res of
                        Right (EvaluationSuccess prog) -> do
                          putStrLn $ inputFile <> " evaluated; result written to " <> outFilePath
                          T.writeFile outFilePath (render $ pretty prog)
                        Right EvaluationFailure      -> do
                          -- warn the user that the file failed to evaluate
                          putStrLn $ inputFile <> " failed to evaluate. Failure written to " <> outFilePath
                          T.writeFile outFilePath shownEvaluationFailure
                        Left _ -> do
                          -- warn the user that exception is thrown
                          putStrLn $ "Exception thrown during evaluation of " <> inputFile <>".Written to " <> outFilePath
                          T.writeFile outFilePath shownEvaluationFailure
      Typecheck ->
        putStrLn "typechecking has not been implemented yet. Only evaluation tests (eval) are supported."
