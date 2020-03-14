{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Cek as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Ck  as PLC
import qualified Language.PlutusCore.Generators             as PLC
import qualified Language.PlutusCore.Generators.Interesting as PLC
import qualified Language.PlutusCore.Generators.Test        as PLC
import qualified Language.PlutusCore.Pretty                 as PLC
import qualified Language.PlutusCore.StdLib.Data.Bool       as PLC
import qualified Language.PlutusCore.StdLib.Data.ChurchNat  as PLC
import qualified Language.PlutusCore.StdLib.Data.Integer    as PLC
import qualified Language.PlutusCore.StdLib.Data.Unit       as PLC

import           Control.Exception                          (toException)
import           Control.Lens
import           Control.Monad
import           Control.Monad.Trans.Except                 (runExceptT)
import           Data.Bifunctor                             (first, second)
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
data EvalMode = CK | CEK deriving (Show, Read)
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
    <> command "example" (info (Example <$> exampleOpts) (progDesc "Show a Plutus Core program example. Usage: first request the list of available examples (optional step), then request a particular example by the name of a type/term. Note that evaluating a generated example may result in 'Failure'"))
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
  <> help "Evaluation mode (CK or CEK)" )

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
    let cfg = PLC.defOnChainConfig & PLC.tccDoNormTypes .~ case mode of
                NotRequired -> True
                Required    -> False
    case (PLC.runQuoteT . PLC.parseTypecheck cfg) bsContents of
        Left (e :: PLC.Error PLC.DefaultUni PLC.AlexPosn) -> do
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
            CK  -> first toException . PLC.extractEvaluationResult . PLC.evaluateCk
            CEK -> first toException . PLC.extractEvaluationResult . PLC.evaluateCek mempty
    case evalFn . void . PLC.toTerm <$> PLC.runQuoteT (PLC.parseScoped bsContents) of
        Left (errCheck :: PLC.Error PLC.DefaultUni PLC.AlexPosn) -> do
            T.putStrLn $ PLC.prettyPlcDefText errCheck
            exitFailure
        Right (Left errEval) -> do
            print errEval
            exitFailure
        Right (Right v) -> do
            T.putStrLn $ PLC.prettyPlcDefText v
            exitSuccess

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TermExample = TermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni ())
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

toTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni () -> TermExample
toTermExample term = TermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    ty = case PLC.runQuote . runExceptT $ PLC.typecheckPipeline PLC.defOffChainConfig program of
        Left (err :: PLC.Error PLC.DefaultUni ()) -> error $ PLC.prettyPlcDefString err
        Right vTy                                 -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni ())]
getInteresting =
    sequence $ PLC.fromInterestingTermGens $ \name gen -> do
        PLC.TermOf term _ <- PLC.getSampleTermValue gen
        pure (T.pack name, term)

simpleExamples :: [(ExampleName, SomeExample)]
simpleExamples =
    [ ("succInteger", SomeTermExample $ toTermExample PLC.succInteger)
    , ("unit"       , SomeTypeExample $ TypeExample (PLC.Type ()) PLC.unit)
    , ("unitval"    , SomeTermExample $ toTermExample PLC.unitval)
    , ("bool"       , SomeTypeExample $ TypeExample (PLC.Type ()) PLC.bool)
    , ("true"       , SomeTermExample $ toTermExample PLC.true)
    , ("false"      , SomeTermExample $ toTermExample PLC.false)
    , ("churchNat"  , SomeTypeExample $ TypeExample (PLC.Type ()) PLC.churchNat)
    , ("churchZero" , SomeTermExample $ toTermExample PLC.churchZero)
    , ("churchSucc" , SomeTermExample $ toTermExample PLC.churchSucc)
    ]

getAvailableExamples :: IO [(ExampleName, SomeExample)]
getAvailableExamples = do
    interesting <- getInteresting
    pure $ simpleExamples ++ map (second $ SomeTermExample . toTermExample) interesting

-- The implementation is a little hacky: we generate interesting examples when the list of examples
-- is requsted and at each lookup of a particular example. I.e. each time we generate distinct
-- terms. But types of those terms must not change across requests, so we're safe.
runExample :: ExampleOptions -> IO ()
runExample (ExampleOptions ExampleAvailable)     = do
    examples <- getAvailableExamples
    traverse_ (T.putStrLn . PLC.docText . uncurry prettySignature) examples
runExample (ExampleOptions (ExampleSingle name)) = do
    examples <- getAvailableExamples
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PLC.docText $ prettyExample ex

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck tos -> runTypecheck tos
        Eval eos      -> runEval eos
        Example eos   -> runExample eos
