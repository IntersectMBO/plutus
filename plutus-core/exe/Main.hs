{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

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

import           Codec.Serialise
import           Control.DeepSeq                            (rnf)
import           Control.Monad
import           Control.Monad.Trans.Except                 (runExceptT)
import           Data.Bifunctor                             (second)
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Foldable                              (traverse_)
import qualified Data.Text                                  as T
import           Data.Text.Encoding                         (encodeUtf8)
import qualified Data.Text.IO                               as T
import           Data.Text.Prettyprint.Doc
import           Options.Applicative
import           System.CPUTime                             (getCPUTime)
import           System.Exit
import           Text.Printf


{- Note [Annotation types] This program now reads and writes
   CBOR-serialised PLC ASTs.  In all cases we require the annotation
   type to be ().  There are two reasons for this.  Firstly, ASTs
   serialised for transmission to the chain will always have unit
   annotations because we can save space by omitting annotations in
   the CBOR (using the OmitUnitAnnotations class from CBOR.hs), so it
   makes sense for the program to deal with these.  Secondly, the
   annotation type has to be specified when we're deserialising CBOR
   (in order to check that the AST has the correct type), so it's
   difficult to deal with CBOR with arbitrary annotation types: fixing
   the annotation type to be () is the simplest thing to do and fits
   our use case.
 -}


type PlainProgram   = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
type ParsedProgram  = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun PLC.AlexPosn
type PlcParserError = PLC.Error PLC.DefaultUni () PLC.AlexPosn


---------------- Option parsers ----------------

data Input = FileInput FilePath | StdInput

input :: Parser Input
input = fileInput <|> stdInput

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "input"
  <> short 'i'
  <> metavar "FILENAME"
  <> help "Input file" )

stdInput :: Parser Input
stdInput = flag' StdInput
  (  long "stdin"
  <> help "Read from stdin" )


data Output = FileOutput FilePath | StdOutput

output :: Parser Output
output = fileOutput <|> stdOutput

fileOutput :: Parser Output
fileOutput = FileOutput <$> strOption
  (  long "output"
  <> short 'o'
  <> metavar "FILENAME"
  <> help "Output file" )

stdOutput :: Parser Output
stdOutput = flag' StdOutput
  (  long "stdout"
  <> help "Write to stdout" )


data Format = Plc | Cbor  -- Input/output format for programs

format :: Parser Format
format = flag Plc Cbor
  ( long "cbor"
  <> long "CBOR"
  <> short 'c'
  <> help "Input ()-annotated CBOR (default: input textual PLC source)"
  )


data Timing = NoTiming | Timing deriving (Eq)  -- Report program execution time?

timing :: Parser Timing
timing = flag NoTiming Timing
  ( long "time-execution"
  <> short 't'
  <> help "Report execution time of program"
  )


data NormalizationMode = Required | NotRequired deriving (Show, Read)
data TypecheckOptions = TypecheckOptions Input Format
data EvalMode = CK | CEK deriving (Show, Read)
data EvalOptions = EvalOptions Input EvalMode Format Timing
data PrintMode = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
data PrintOptions = PrintOptions Input PrintMode
data PlcToCborOptions = PlcToCborOptions Input Output
data CborToPlcOptions = CborToPlcOptions Input Output PrintMode
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
newtype ExampleOptions = ExampleOptions ExampleMode

-- Main commands
data Command = Typecheck TypecheckOptions
             | Eval EvalOptions
             | Example ExampleOptions
             | Print PrintOptions
             | PlcToCbor PlcToCborOptions
             | CborToPlc CborToPlcOptions

helpText :: String
helpText =
    "This program provides a number of utilities for dealing with "
    ++ "Plutus Core programs, including typechecking, evaluation, and conversion "
    ++ "between various formats.  The program also provides a number of example "
    ++ "Plutus Core progrrams.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in CBOR format: ASTs are always written with "
    ++ "unit annotations, and any CBOR-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a CBOR AST with any "
    ++ "non-unit annotation type will cause an error."

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (fullDesc <> header "Plutus Core tool" <> progDesc helpText)

plutusOpts :: Parser Command
plutusOpts = hsubparser (
    command "typecheck" (info (Typecheck <$> typecheckOpts) (progDesc "Typecheck a Plutus Core program"))
    <> command "evaluate" (info (Eval <$> evalOpts) (progDesc "Evaluate a Plutus Core program"))
    <> command "example" (info (Example <$> exampleOpts) (progDesc "Show a Plutus Core program example. Usage: first request the list of available examples (optional step), then request a particular example by the name of a type/term. Note that evaluating a generated example may result in 'Failure'"))
    <> command "print" (info (Print <$> printOpts) (progDesc "Parse a program then prettyprint it"))
    <> command "plc-to-cbor" (info (PlcToCbor <$> plcToCborOpts) (progDesc "Convert a PLC source file to ()-annotated CBOR"))
    <> command "cbor-to-plc" (info (CborToPlc <$> cborToPlcOpts) (progDesc "Convert a ()-annotated CBOR file to PLC source"))
  )

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> format

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CEK
  <> showDefault
  <> help "Evaluation mode (CK or CEK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOptions <$> input <*> evalMode <*> format <*> timing

printMode :: Parser PrintMode
printMode = option auto
  (  long "print-mode"
  <> metavar "MODE"
  <> value Classic
  <> showDefault
  <> help ("Print mode: Classic -> plcPrettyClassicDef, Debug -> plcPrettyClassicDebug, "
        ++ "Readable -> prettyPlcReadableDef, ReadableDebug -> prettyPlcReadableDebug" ))

printOpts :: Parser PrintOptions
printOpts = PrintOptions <$> input <*> printMode

plcToCborOpts :: Parser PlcToCborOptions
plcToCborOpts = PlcToCborOptions <$> input <*> output

cborToPlcOpts :: Parser CborToPlcOptions
cborToPlcOpts = CborToPlcOptions <$> input <*> output <*> printMode

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


---------------- Reading programs from files ----------------

-- Read a PLC source file
getPlcInput :: Input -> IO String
getPlcInput (FileInput file) = readFile file
getPlcInput StdInput         = getContents

-- Read and parse a PLC source file
parsePlcFile :: Input -> IO ParsedProgram
parsePlcFile inp = do
    contents <- getPlcInput inp
    let bsContents = (BSL.fromStrict . encodeUtf8 . T.pack) contents
    case PLC.runQuoteT $ runExceptT (PLC.parseScoped bsContents) of
        Left (errCheck :: PlcParserError) -> do
            T.putStrLn $ PLC.displayPlcDef errCheck
            exitFailure
        Right (Left (errEval :: PlcParserError)) -> do
            print errEval
            exitFailure
        Right (Right (p :: ParsedProgram)) ->
            return p

-- Read a PLC AST from a CBOR file
getCborInput :: Input -> IO BSL.ByteString
getCborInput StdInput         = BSL.getContents
getCborInput (FileInput file) = BSL.readFile file


-- Load a PLC AST from a CBOR file
loadPlcFromCborFile :: Input -> IO PlainProgram
loadPlcFromCborFile inp = do
  p <- getCborInput inp -- The type is constrained in the Right case below.
  case deserialiseOrFail p of
    Left (DeserialiseFailure offset msg) ->
        do
          putStrLn $ "Deserialisation failure at offset " ++ show offset ++ ": " ++ msg
          exitFailure
    Right (r::PlainProgram) -> return r


-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProg :: Input -> Format -> IO ParsedProgram
getProg inp fmt =
    case fmt of
      Plc  -> parsePlcFile inp
      Cbor -> do
               plc <-loadPlcFromCborFile inp
               return (fakeAlexPosn <$ plc)  -- Adjust the return type to ParsedProgram
                   where fakeAlexPosn = PLC.AlexPn 0 0 0


---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  prog <- getProg inp fmt
  case PLC.runQuoteT $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.typecheckPipeline tcConfig (void prog)
    of
       Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) -> do
           putStrLn $ PLC.displayPlcDef e
           exitFailure
       Right ty -> do
           T.putStrLn $ PLC.displayPlcDef ty
           exitSuccess


---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp mode fmt printtime) = do
  prog <- getProg inp fmt
  let evalFn = case mode of
                 CK  -> PLC.unsafeEvaluateCk  PLC.defBuiltinsRuntime
                 CEK -> PLC.unsafeEvaluateCek PLC.defBuiltinsRuntime
      body = void . PLC.toTerm $ prog
      _ = rnf body   -- Force evaluation of body to ensure that we're not timing parsing/deserialisation
  start <- getCPUTime
  case evalFn body of
    PLC.EvaluationSuccess v -> do
      end <- getCPUTime
      let ms = 1e9 :: Double
          diff = (fromIntegral (end - start)) / ms
      T.putStrLn $ PLC.displayPlcDef v
      when (printtime == Timing) $ printf "Evaluation time: %0.2f ms\n" diff
      exitSuccess
    PLC.EvaluationFailure -> exitFailure


---------------- Parse and print a PLC source file ----------------

getPrintMethod :: PLC.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PLC.prettyPlcClassicDef
      Debug         -> PLC.prettyPlcClassicDebug
      Readable      -> PLC.prettyPlcReadableDef
      ReadableDebug -> PLC.prettyPlcReadableDebug

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions inp mode) =
  let
  in do
    p <- parsePlcFile inp
    print . (getPrintMethod mode) $ p


---------------- Convert a PLC source file to CBOR ----------------

runPlcToCbor :: PlcToCborOptions -> IO ()
runPlcToCbor (PlcToCborOptions inp outp) = do
  p <- parsePlcFile inp
  let cbor = serialise (() <$ p) -- Change annotations to (): see Note [Annotation types].
  case outp of
    FileOutput file -> BSL.writeFile file cbor
    StdOutput       -> BSL.putStr cbor *> putStrLn ""


---------------- Convert a CBOR file to PLC source ----------------

runCborToPlc :: CborToPlcOptions -> IO ()
runCborToPlc (CborToPlcOptions inp outp mode) = do
  plc <- loadPlcFromCborFile inp
  let printMethod = getPrintMethod mode
  case outp of
    FileOutput file -> writeFile file . show . printMethod $ plc
    StdOutput       -> print . printMethod $ plc


---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TermExample = TermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())
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

toTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun () -> TermExample
toTermExample term = TermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    ty =
        case PLC.runQuote . runExceptT $ do
            tcConfig <- PLC.getDefTypeCheckConfig ()
            PLC.typecheckPipeline tcConfig program
        of
          Left (err :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) -> error $ PLC.displayPlcDef err
          Right vTy                                                -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())]
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
    traverse_ (T.putStrLn . PLC.render . uncurry prettySignature) examples
runExample (ExampleOptions (ExampleSingle name)) = do
    examples <- getAvailableExamples
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PLC.render $ prettyExample ex


---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck tos  -> runTypecheck tos
        Eval eos       -> runEval eos
        Example eos    -> runExample eos
        Print dos      -> runPrint dos
        PlcToCbor opts -> runPlcToCbor opts
        CborToPlc opts -> runCborToPlc opts
