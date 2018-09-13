{-# LANGUAGE FlexibleContexts #-}
module Main (main) where

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.Evaluation.CkMachine   as PLC
import qualified Language.PlutusCore.Interpreter.CekMachine as PLC

import           Control.Monad

import qualified Data.ByteString.Lazy                       as BSL
import           Data.Semigroup                             ((<>))
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

newtype TypecheckOptions = TypecheckOptions Input
data EvalMode = CK | CEK deriving (Show, Read)
data EvalOptions = EvalOptions Input EvalMode
data Command = Typecheck TypecheckOptions | Eval EvalOptions

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (progDesc "Plutus Core tool")

plutusOpts :: Parser Command
plutusOpts = hsubparser (
    command "typecheck" (info (Typecheck <$> typecheckOpts) (progDesc "Typecheck a Plutus Core program"))
    <> command "evaluate" (info (Eval <$> evalOpts) (progDesc "Evaluate a Plutus Core program"))
  )

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CEK
  <> showDefault
  <> help "Evaluation mode (one of CK or CEK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOptions <$> input <*> evalMode

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck (TypecheckOptions inp) -> do
            contents <- getInput inp
            let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
            case (PLC.runQuoteT . PLC.parseTypecheck 1000) bsContents of
                Left e -> do
                    T.putStrLn $ PLC.prettyCfgText e
                    exitFailure
                Right ty -> do
                    T.putStrLn $ PLC.prettyCfgText ty
                    exitSuccess
        Eval (EvalOptions inp mode) -> do
            contents <- getInput inp
            let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
            let evalFn = case mode of
                    CK  -> PLC.runCk
                    CEK -> PLC.runCek
            case evalFn .void <$> PLC.parseScoped bsContents of
                Left e -> do
                    T.putStrLn $ PLC.prettyCfgText e
                    exitFailure
                Right v -> do
                    T.putStrLn $ PLC.prettyCfgText v
                    exitSuccess
