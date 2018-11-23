{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.Evaluation.CkMachine   as PLC
import qualified Language.PlutusCore.Interpreter.CekMachine as PLC
import qualified Language.PlutusCore.Interpreter.LMachine   as PLC
import qualified Language.PlutusCore.Pretty                 as PLC

import           Control.Monad

import qualified Data.ByteString.Lazy                       as BSL
import qualified Data.Text                                  as T
import           Data.Text.Encoding                         (encodeUtf8)
import qualified Data.Text.IO                               as T

import           System.Exit

import           Options.Applicative

data Input = FileInput FilePath | StdInput

getInput :: Input -> IO String
getInput (FileInput s) = readFile s
getInput StdInput      = getContents

input :: Parser Input
input = fileInput <|> stdInput

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "file"
  <> short 'f'
  <> metavar "FILENAME"
  <> help "Input file" )

stdInput :: Parser Input
stdInput = flag' StdInput
  (  long "stdin"
  <> help "Read from stdin" )

data NormalizationMode = Required | NotRequired deriving (Show, Read)
data TypecheckOptions = TypecheckOptions Input NormalizationMode
data EvalMode = CK | CEK | L deriving (Show, Read)
data EvalOptions = EvalOptions Input EvalMode
data Command = Typecheck TypecheckOptions | Eval EvalOptions

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (progDesc "Plutus Core tool")

plutusOpts :: Parser Command
plutusOpts = hsubparser (
    command "typecheck" (info (Typecheck <$> typecheckOpts) (progDesc "Typecheck a Plutus Core program"))
    <> command "evaluate" (info (Eval <$> evalOpts) (progDesc "Evaluate a Plutus Core program"))
  )

normalizationMode :: Parser NormalizationMode
normalizationMode = option auto
  (  long "normalized-types"
  <> metavar "MODE"
  <> value NotRequired
  <> showDefault
  <> help "Whether type annotations must be normalized or not (one of Required or NotRequired)" )

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> normalizationMode

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CEK
  <> showDefault
  <> help "Evaluation mode (one of CK, CEK or L)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOptions <$> input <*> evalMode

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp mode) = do
    contents <- getInput inp
    let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
    let cfg = PLC.TypeCheckCfg PLC.defaultTypecheckerGas $ PLC.TypeConfig (case mode of {NotRequired -> True; Required -> False}) mempty
    case (PLC.runQuoteT . PLC.parseTypecheck cfg) bsContents of
        Left (e :: PLC.Error PLC.AlexPosn) -> do
            T.putStrLn $ PLC.prettyPlcDefText e
            exitFailure
        Right ty -> do
            T.putStrLn $ PLC.prettyPlcDefText ty
            exitSuccess

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp mode) = do
    contents <- getInput inp
    let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
    let evalFn = case mode of
            CK  -> PLC.runCk
            CEK -> PLC.runCek mempty
            L   -> PLC.runL
    case evalFn .void <$> PLC.parseScoped bsContents of
        Left (e :: PLC.Error PLC.AlexPosn) -> do
            T.putStrLn $ PLC.prettyPlcDefText e
            exitFailure
        Right v -> do
            T.putStrLn $ PLC.prettyPlcDefText v
            exitSuccess

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck tos -> runTypecheck tos
        Eval eos      -> runEval eos
