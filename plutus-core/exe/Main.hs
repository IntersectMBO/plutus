{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module Main (main) where

import qualified Language.PlutusCore                                        as PLC
import           Language.PlutusCore.CBOR
import qualified Language.PlutusCore.Constant.Dynamic                       as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Cek                 as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Ck                  as PLC
import qualified Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC
import qualified Language.PlutusCore.Generators                             as PLC
import qualified Language.PlutusCore.Generators.Interesting                 as PLC
import qualified Language.PlutusCore.Generators.Test                        as PLC
import qualified Language.PlutusCore.Pretty                                 as PLC
import qualified Language.PlutusCore.StdLib.Data.Bool                       as PLC
import qualified Language.PlutusCore.StdLib.Data.ChurchNat                  as PLC
import qualified Language.PlutusCore.StdLib.Data.Integer                    as PLC
import qualified Language.PlutusCore.StdLib.Data.Unit                       as PLC
import qualified Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC

import           Codec.Serialise
import           Control.DeepSeq                                            (rnf)
import qualified Control.Exception                                          (evaluate)
import           Control.Monad
import           Control.Monad.Trans.Except                                 (runExceptT)
import           Data.Bifunctor                                             (second)
import qualified Data.ByteString.Lazy                                       as BSL
import           Data.Foldable                                              (traverse_)
import           Data.Functor                                               ((<&>))
import qualified Data.Text                                                  as T
import           Data.Text.Encoding                                         (encodeUtf8)
import qualified Data.Text.IO                                               as T
import           Data.Text.Prettyprint.Doc
import           Options.Applicative
import           System.CPUTime                                             (getCPUTime)
import           System.Exit
import           System.IO
import           Text.Printf

{- Note [Annotation types] This program now reads and writes CBOR-serialised PLC
   ASTs.  In all cases we require the annotation type to be ().  There are two
   reasons for this.  Firstly, ASTs serialised for transmission to the chain
   will always have unit annotations because we can save space by omitting
   annotations in the CBOR (using the OmitUnitAnnotations class from CBOR.hs),
   so it makes sense for the program to deal with these.  Secondly, the
   annotation type has to be specified when we're deserialising CBOR (in order
   to check that the AST has the correct type), so it's difficult to deal with
   CBOR with arbitrary annotation types: fixing the annotation type to be () is
   the simplest thing to do and fits our use case.
 -}

type TypedProgram a = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni a
type UntypedProgram a = UPLC.Program PLC.Name PLC.DefaultUni a

data Program a =
      TypedProgram (TypedProgram a)
    | UntypedProgram (UntypedProgram a)
    deriving (Functor)

instance (PLC.PrettyBy PLC.PrettyConfigPlc (Program a)) where
    prettyBy cfg (TypedProgram p)   = PLC.prettyBy cfg p
    prettyBy cfg (UntypedProgram p) = PLC.prettyBy cfg p

type PlcParserError = PLC.Error PLC.DefaultUni PLC.AlexPosn


---------------- Option parsers ----------------

data Language = TypedPLC | UntypedPLC

typedPLC :: Parser Language
typedPLC = flag UntypedPLC TypedPLC (long "typed" <> short 't' <> help "Use typed Plutus Core")

untypedPLC :: Parser Language
untypedPLC = flag UntypedPLC UntypedPLC (long "untyped" <> short 'u' <> help "Use untyped Plutus Core (default)")
-- ^ NB: default is always UntypedPLC

languageMode :: Parser Language
languageMode = typedPLC <|> untypedPLC

data Input = FileInput FilePath | StdInput

-- | Parser for an input stream. If none is specified, default to stdin: this makes use in pipelines easier
input :: Parser Input
input = fileInput <|> stdInput <|> pure StdInput

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "input"
  <> short 'i'
  <> metavar "FILENAME"
  <> help "Input file" )

stdInput :: Parser Input
stdInput = flag' StdInput
  (  long "stdin"
  <> help "Read from stdin (default)" )


data Output = FileOutput FilePath | StdOutput

-- | Parser for an output stream. If none is specified, default to stdout: this makes use in pipelines easier
output :: Parser Output
output = fileOutput <|> stdOutput <|> pure StdOutput

fileOutput :: Parser Output
fileOutput = FileOutput <$> strOption
  (  long "output"
  <> short 'o'
  <> metavar "FILENAME"
  <> help "Output file" )

stdOutput :: Parser Output
stdOutput = flag' StdOutput
  (  long "stdout"
  <> help "Write to stdout (default)" )


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
  <> short 'x'
  <> help "Report execution time of program"
  )

data NormalizationMode = Required | NotRequired deriving (Show, Read)
data TypecheckOptions = TypecheckOptions Input Format
data PlcToCborOptions = PlcToCborOptions Language Input Output
data CborToPlcOptions = CborToPlcOptions Language Input Output PrintMode
data PrintMode = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
data PrintOptions = PrintOptions Language Input PrintMode
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
newtype ExampleOptions = ExampleOptions ExampleMode
data EraseOptions = EraseOptions Input Output Format PrintMode
data EvalMode = CK | CEK deriving (Show, Read)
data EvalOptions = EvalOptions Language Input EvalMode Format Timing

-- Main commands
data Command = Typecheck TypecheckOptions
             | PlcToCbor PlcToCborOptions
             | CborToPlc CborToPlcOptions
             | Print PrintOptions
             | Example ExampleOptions
             | Erase EraseOptions
             | Eval EvalOptions


helpText :: String
helpText =
    "This program provides a number of utilities for dealing with "
    ++ "Plutus Core programs, including typechecking, evaluation, and conversion "
    ++ "between various formats.  The program also provides a number of example "
    ++ "typed Plutus Core programs.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in CBOR format: ASTs are always written with "
    ++ "unit annotations, and any CBOR-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a CBOR AST with any "
    ++ "non-unit annotation type will cause an error."

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (fullDesc <> header "Plutus Core tool" <> progDesc helpText)

plutusOpts :: Parser Command
plutusOpts = hsubparser (
       command "print"
           (info (Print <$> printOpts)
            (progDesc "Parse a program then prettyprint it."))
    <> command "plc-to-cbor"
           (info (PlcToCbor <$> plcToCborOpts)
            (progDesc "Convert a PLC source file to ()-annotated CBOR."))
    <> command "cbor-to-plc"
           (info (CborToPlc <$> cborToPlcOpts)
            (progDesc "Convert a ()-annotated CBOR file to PLC source."))
    <> command "example"
           (info (Example <$> exampleOpts)
            (progDesc $ "Show a typed Plutus Core program example. "
                     ++ "Usage: first request the list of available examples (optional step), "
                     ++ "then request a particular example by the name of a type/term. "
                     ++ "Note that evaluating a generated example may result in 'Failure'."))
    <> command "typecheck"
           (info (Typecheck <$> typecheckOpts)
            (progDesc "Typecheck a typed Plutus Core program."))
    <> command "erase"
           (info (Erase <$> eraseOpts)
            (progDesc "Convert a typed Plutus Core program to an untyped one."))
    <> command "evaluate"
           (info (Eval <$> evalOpts)
            (progDesc "Evaluate a Plutus Core program."))
  )

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> format

printMode :: Parser PrintMode
printMode = option auto
  (  long "print-mode"
  <> metavar "MODE"
  <> value Classic
  <> showDefault
  <> help ("Print mode: Classic -> plcPrettyClassicDef, Debug -> plcPrettyClassicDebug, "
        ++ "Readable -> prettyPlcReadableDef, ReadableDebug -> prettyPlcReadableDebug" ))

printOpts :: Parser PrintOptions
printOpts = PrintOptions <$> languageMode <*> input <*> printMode

plcToCborOpts :: Parser PlcToCborOptions
plcToCborOpts = PlcToCborOptions <$> languageMode <*> input <*> output

cborToPlcOpts :: Parser CborToPlcOptions
cborToPlcOpts = CborToPlcOptions <$> languageMode <*> input <*> output <*> printMode

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

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CEK
  <> showDefault
  <> help "Evaluation mode (CK or CEK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOptions <$> languageMode <*> input <*> evalMode <*> format <*> timing

eraseOpts :: Parser EraseOptions
eraseOpts = EraseOptions <$> input <*> output <*> format <*> printMode


---------------- Reading programs from files ----------------

-- Read a PLC source program
getPlcInput :: Input -> IO String
getPlcInput (FileInput file) = readFile file
getPlcInput StdInput         = getContents

-- Read and parse a PLC source program
parsePlcInput :: Language -> Input -> IO (Program PLC.AlexPosn)
parsePlcInput language inp = do
    bsContents <- BSL.fromStrict . encodeUtf8 . T.pack <$> getPlcInput inp
    case language of
      TypedPLC   -> handleResult TypedProgram   $ PLC.runQuoteT $ runExceptT (PLC.parseScoped bsContents)
      UntypedPLC -> handleResult UntypedProgram $ PLC.runQuoteT $ runExceptT (UPLC.parseScoped bsContents)
      where handleResult wrapper =
                \case
                  Left errCheck        -> failWith errCheck
                  Right (Left errEval) -> failWith errEval
                  Right (Right p)      -> return $ wrapper p
            failWith (err :: PlcParserError) =  T.hPutStrLn stderr (PLC.displayPlcDef err) >> exitFailure


-- Read a CBOR-encoded PLC AST
getCborInput :: Input -> IO BSL.ByteString
getCborInput StdInput         = BSL.getContents
getCborInput (FileInput file) = BSL.readFile file

-- Read and deserialise a CBOR-encoded AST
loadASTfromCBOR :: Language -> Input -> IO (Program ())
loadASTfromCBOR language inp =
    case language of
         TypedPLC   -> getCborInput inp <&> deserialiseOrFail >>= handleResult TypedProgram
         UntypedPLC -> getCborInput inp <&> deserialiseOrFail >>= handleResult UntypedProgram
    where handleResult wrapper =
              \case
                Left (DeserialiseFailure offset msg) ->
                    hPutStrLn stderr ("Deserialisation failure at offset " ++ show offset ++ ": " ++ msg) >> exitFailure
                Right r -> return $ wrapper r

-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram :: Language -> Input -> Format -> IO (Program PLC.AlexPosn)
getProgram language inp fmt =
    case fmt of
      Plc  -> parsePlcInput language inp
      Cbor -> do
               prog <- loadASTfromCBOR language inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.


---------------- Parse and print a PLC source file ----------------

getPrintMethod :: PLC.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PLC.prettyPlcClassicDef
      Debug         -> PLC.prettyPlcClassicDebug
      Readable      -> PLC.prettyPlcReadableDef
      ReadableDebug -> PLC.prettyPlcReadableDebug

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions language inp mode) =
    parsePlcInput language inp >>= print . (getPrintMethod mode)


---------------- Convert a PLC source file to CBOR ----------------

serialiseProgram :: Serialise a => Program a -> BSL.ByteString
serialiseProgram (TypedProgram p)   = serialise p
serialiseProgram (UntypedProgram p) = serialise p

writeCBOR :: Output -> Program a -> IO ()
writeCBOR outp prog = do
  let cbor = serialiseProgram (() <$ prog) -- Change annotations to (): see Note [Annotation types].
  case outp of
    FileOutput file -> BSL.writeFile file cbor
    StdOutput       -> BSL.putStr cbor >> T.putStrLn ""

runPlcToCbor :: PlcToCborOptions -> IO ()
runPlcToCbor (PlcToCborOptions language inp outp) =
  parsePlcInput language inp >>= writeCBOR outp


---------------- Convert a CBOR file to PLC source ----------------

writePlc :: Output -> PrintMode -> Program a -> IO ()
writePlc outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog

runCborToPlc :: CborToPlcOptions -> IO ()
runCborToPlc (CborToPlcOptions language inp outp mode) =
  loadASTfromCBOR language inp >>= writePlc outp mode


---------------- Examples ----------------

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
    ty = case PLC.runQuote . runExceptT $ PLC.typecheckPipeline PLC.defConfig program of
        Left (err :: PLC.Error PLC.DefaultUni ()) -> error $ PLC.displayPlcDef err
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
    traverse_ (T.putStrLn . PLC.render . uncurry prettySignature) examples
runExample (ExampleOptions (ExampleSingle name)) = do
    examples <- getAvailableExamples
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PLC.render $ prettyExample ex


---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  TypedProgram prog <- getProgram TypedPLC inp fmt
  case PLC.runQuoteT $ do
    types <- PLC.getStringBuiltinTypes ()
    PLC.typecheckPipeline (PLC.TypeCheckConfig types) (void prog)
    of
       Left (e :: PLC.Error PLC.DefaultUni ()) -> T.hPutStrLn stderr (PLC.displayPlcDef e) >> exitFailure
       Right ty                                -> T.putStrLn (PLC.displayPlcDef ty) >> exitSuccess


---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions language inp mode fmt printtime) =
    case language of

      TypedPLC -> do
        TypedProgram prog <- getProgram TypedPLC inp fmt
        let evaluate = case mode of
                          CK  -> PLC.unsafeEvaluateCk  (PLC.getStringBuiltinMeanings @ (PLC.CkValue  PLC.DefaultUni))
                          CEK -> PLC.unsafeEvaluateCek (PLC.getStringBuiltinMeanings @ (PLC.CekValue PLC.DefaultUni)) PLC.defaultCostModel
            body = void . PLC.toTerm $ prog
        () <-  Control.Exception.evaluate $ rnf body
        -- ^ Force evaluation of body to ensure that we're not timing parsing/deserialisation.
        -- The parser apparently returns a fully-evaluated AST, but let's be on the safe side.
        start <- getCPUTime
        case evaluate body of
              PLC.EvaluationSuccess v -> succeed start v
              PLC.EvaluationFailure   -> exitFailure

      UntypedPLC ->
          case mode of
            CK  -> hPutStrLn stderr "There is no CK machine for UntypedPLC Plutus Core" >> exitFailure
            CEK -> do
                  UntypedProgram prog <- getProgram UntypedPLC inp fmt
                  let evaluate = UPLC.unsafeEvaluateCek (PLC.getStringBuiltinMeanings @ (UPLC.CekValue PLC.DefaultUni)) PLC.defaultCostModel
                      body = void . UPLC.toTerm $ prog
                  () <- Control.Exception.evaluate $ rnf body
                  start <- getCPUTime
                  case evaluate body of
                    UPLC.EvaluationSuccess v -> succeed start v
                    UPLC.EvaluationFailure   -> exitFailure

    where succeed start v = do
            end <- getCPUTime
            T.putStrLn $ PLC.displayPlcDef v
            let ms = 1e9 :: Double
                diff = (fromIntegral (end - start)) / ms
            when (printtime == Timing) $ printf "Evaluation time: %0.2f ms\n" diff
            exitSuccess

---------------- Erasure ----------------

-- | Input a program, erase the types, then output it in the same format
-- (ie, if we input text then output text; if we input CBOR then output CBOR)
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp outp fmt mode) = do
  TypedProgram typedProg <- getProgram TypedPLC inp fmt
  let untypedProg = UntypedProgram $ UPLC.eraseProgram typedProg
  case fmt of
    Plc  -> writePlc outp mode untypedProg
    Cbor -> writeCBOR outp untypedProg


---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Typecheck opts -> runTypecheck opts
        Eval      opts -> runEval      opts
        Example   opts -> runExample   opts
        Erase     opts -> runErase     opts
        Print     opts -> runPrint     opts
        PlcToCbor opts -> runPlcToCbor opts
        CborToPlc opts -> runCborToPlc opts
