{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.Evaluation.CkMachine   as PLC
import qualified Language.PlutusCore.Interpreter.CekMachine as PLC
import qualified Language.PlutusCore.Interpreter.LMachine   as PLC
import qualified Language.PlutusCore.Pretty                 as PLC
import qualified Language.PlutusCore.StdLib.Data.Bool       as PLC
import qualified Language.PlutusCore.StdLib.Data.ChurchNat  as PLC
import qualified Language.PlutusCore.StdLib.Data.Integer    as PLC
import qualified Language.PlutusCore.StdLib.Data.Unit       as PLC

import           Control.Monad
import           Control.Monad.Trans.Except                 (runExceptT)
import           Data.Foldable                              (traverse_)

import qualified Data.ByteString.Lazy                       as BSL
import qualified Data.Text                                  as T
import           Data.Text.Encoding                         (encodeUtf8)
import qualified Data.Text.IO                               as T
import           Data.Text.Prettyprint.Doc

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
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
newtype ExampleOptions = ExampleOptions ExampleMode
data Command = Typecheck TypecheckOptions | Eval EvalOptions | Example ExampleOptions

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (progDesc "Plutus Core tool")

plutusOpts :: Parser Command
plutusOpts = hsubparser (
    command "typecheck" (info (Typecheck <$> typecheckOpts) (progDesc "Typecheck a Plutus Core program"))
    <> command "evaluate" (info (Eval <$> evalOpts) (progDesc "Evaluate a Plutus Core program"))
    <> command "example" (info (Example <$> exampleOpts) (progDesc "Show a Plutus Core program example"))
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

exampleMode :: Parser ExampleMode
exampleMode = exampleAvailable <|> exampleSingle

exampleAvailable :: Parser ExampleMode
exampleAvailable = flag' ExampleAvailable
  (  long "available"
  <> short 'a'
  <> help "Show available examples")

exampleName :: Parser ExampleName
exampleName = strOption
  (  long "single"
  <> metavar "NAME"
  <> short 's'
  <> help "Show a single example")

exampleSingle :: Parser ExampleMode
exampleSingle = ExampleSingle <$> exampleName

exampleOpts :: Parser ExampleOptions
exampleOpts = ExampleOptions <$> exampleMode

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp mode) = do
    contents <- getInput inp
    let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
    let cfg = PLC.TypeConfig (case mode of {NotRequired -> True; Required -> False}) mempty PLC.defaultTypecheckerGas
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
            L   -> PLC.runL mempty
    case evalFn . void <$> PLC.runQuoteT (PLC.parseScoped bsContents) of
        Left (e :: PLC.Error PLC.AlexPosn) -> do
            T.putStrLn $ PLC.prettyPlcDefText e
            exitFailure
        Right v -> do
            T.putStrLn $ PLC.prettyPlcDefText v
            exitSuccess

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName ())
data TermExample = TermExample (PLC.Type PLC.TyNameWithKind ()) (PLC.Term PLC.TyName PLC.Name ())
data SomeExample = SomeTypeExample TypeExample | SomeTermExample TermExample

prettySignature :: ExampleName -> SomeExample -> Doc ann
prettySignature name (SomeTypeExample (TypeExample kind _)) =
    pretty name <+> "::" <+> PLC.prettyPlcDef kind
prettySignature name (SomeTermExample (TermExample ty _)) =
    pretty name <+> ":"  <+> PLC.prettyPlcDef ty

prettyExample :: SomeExample -> Doc ann
prettyExample (SomeTypeExample (TypeExample _ ty))   = PLC.prettyPlcDef ty
prettyExample (SomeTermExample (TermExample _ term)) =
    PLC.prettyPlcDef $ PLC.Program () (PLC.defaultVersion ()) term

toTermExample :: PLC.Quote (PLC.Term PLC.TyName PLC.Name ()) -> TermExample
toTermExample getTerm = TermExample ty term where
    term = PLC.runQuote getTerm
    program = PLC.Program () (PLC.defaultVersion ()) term
    config = PLC.TypeConfig True mempty Nothing
    ty = case PLC.runQuote . runExceptT $ PLC.typecheckPipeline config program of
        Left (err :: PLC.Error ()) -> error $ PLC.prettyPlcDefString err
        Right vTy                  -> PLC.getNormalizedType vTy

availableExamples :: [(ExampleName, SomeExample)]
availableExamples =
    [ ("succInteger", SomeTermExample $ toTermExample PLC.getBuiltinSuccInteger)
    , ("unit"       , SomeTypeExample $ TypeExample (PLC.Type ()) unit)
    , ("unitval"    , SomeTermExample $ toTermExample PLC.getBuiltinUnitval)
    , ("bool"       , SomeTypeExample $ TypeExample (PLC.Type ()) bool)
    , ("true"       , SomeTermExample $ toTermExample PLC.getBuiltinTrue)
    , ("false"      , SomeTermExample $ toTermExample PLC.getBuiltinFalse)
    , ("churchNat"  , SomeTypeExample $ TypeExample (PLC.Type ()) churchNat)
    , ("churchZero" , SomeTermExample $ toTermExample PLC.getBuiltinChurchZero)
    , ("churchSucc" , SomeTermExample $ toTermExample PLC.getBuiltinChurchSucc)
    ] where
        unit = PLC.runQuote PLC.getBuiltinUnit
        bool = PLC.runQuote PLC.getBuiltinBool
        churchNat = PLC.runQuote PLC.getBuiltinChurchNat

runExample :: ExampleOptions -> IO ()
runExample (ExampleOptions ExampleAvailable)     =
    traverse_ (T.putStrLn . PLC.docText . uncurry prettySignature) availableExamples
runExample (ExampleOptions (ExampleSingle name)) =
    T.putStrLn $ case lookup name availableExamples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PLC.docText $ prettyExample ex

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck tos -> runTypecheck tos
        Eval eos      -> runEval eos
        Example eos   -> runExample eos
