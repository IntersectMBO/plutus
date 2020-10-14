{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module Main (main) where

import qualified Language.PlutusCore                                        as PLC
import           Language.PlutusCore.CBOR
import qualified Language.PlutusCore.Constant.Dynamic                       as PLC
import qualified Language.PlutusCore.DeBruijn                               as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Cek                 as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Ck                  as PLC
import qualified Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC
import qualified Language.PlutusCore.Generators                             as Gen
import qualified Language.PlutusCore.Generators.Interesting                 as Gen
import qualified Language.PlutusCore.Generators.Test                        as Gen
import qualified Language.PlutusCore.Pretty                                 as PP
import qualified Language.PlutusCore.StdLib.Data.Bool                       as StdLib
import qualified Language.PlutusCore.StdLib.Data.ChurchNat                  as StdLib
import qualified Language.PlutusCore.StdLib.Data.Integer                    as StdLib
import qualified Language.PlutusCore.StdLib.Data.Unit                       as StdLib
import qualified Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn                        as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC

import           Codec.Serialise
import           Control.DeepSeq                                            (rnf)
import qualified Control.Exception                                          as Exn (evaluate)
import           Control.Monad
import           Control.Monad.Trans.Except                                 (runExceptT)
import           Data.Bifunctor                                             (second)
import qualified Data.ByteString.Lazy                                       as BSL
import           Data.Foldable                                              (traverse_)
import           Data.Functor                                               ((<&>))
import qualified Data.Text                                                  as T
import           Data.Text.Encoding                                         (encodeUtf8)
import qualified Data.Text.IO                                               as T
import           Data.Text.Prettyprint.Doc                                  (Doc, pretty, (<+>))
import           Options.Applicative
import           System.CPUTime                                             (getCPUTime)
import           System.Exit                                                (exitFailure, exitSuccess)
import           System.IO
import           System.Mem                                                 (performGC)
import           Text.Printf                                                (printf)

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


-- | Our internal representation of programs is as ASTs over the Name type.
-- We may change this to ASTs with nameless deBruijn indices/levels at some point
type TypedProgram a = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni a
type UntypedProgram a = UPLC.Program PLC.Name PLC.DefaultUni a

data Program a =
      TypedProgram (TypedProgram a)
    | UntypedProgram (UntypedProgram a)
    deriving (Functor)

instance (PP.PrettyBy PP.PrettyConfigPlc (Program a)) where
    prettyBy cfg (TypedProgram p)   = PP.prettyBy cfg p
    prettyBy cfg (UntypedProgram p) = PP.prettyBy cfg p

type TypedProgramDeBruijn a = PLC.Program PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni a
type UntypedProgramDeBruijn a = UPLC.Program UPLC.DeBruijn PLC.DefaultUni a

data ProgramDeBruijn a =
      TypedProgramDeBruijn (TypedProgramDeBruijn a)
    | UntypedProgramDeBruijn (UntypedProgramDeBruijn a)
    deriving (Functor)


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

data CborMode = Named | DeBruijn

data Format = Plc | Cbor CborMode -- Input/output format for programs
instance Prelude.Show Format where
    show Plc             = "plc"
    show (Cbor Named)    = "cbor-named"
    show (Cbor DeBruijn) = "cbor-deBruijn"

inputformat :: Parser Format
inputformat = option (maybeReader formatReader)
  (  long "if"
  <> long "input-format"
  <> metavar "FORMAT"
  <> value Plc
  <> showDefault
  <> help ("Input format: " ++ formatHelp))

outputformat :: Parser Format
outputformat = option (maybeReader formatReader)
  (  long "of"
  <> long "output-format"
  <> metavar "FORMAT"
  <> value Plc
  <> showDefault
  <> help ("Output format: " ++ formatHelp))

formatHelp :: String
formatHelp = "plc, cbor (deBruijn indices), or cbor-named (names)"

formatReader :: String -> Maybe Format
formatReader s =
    if s `elem` ["plc", "PLC"]
    then Just Plc
    else
        if s `elem` ["CBOR-full", "cbor-full"]
         then Just (Cbor Named)
         else
             if s `elem` ["CBOR", "cbor","cbor-deBruijn"]
             then Just (Cbor DeBruijn)
             else Nothing

data Timing = NoTiming | Timing deriving (Eq)  -- Report program execution time?

timing :: Parser Timing
timing = flag NoTiming Timing
  ( long "time-execution"
  <> short 'x'
  <> help "Report execution time of program"
  )

data NormalizationMode = Required | NotRequired deriving (Show, Read)
data TypecheckOptions = TypecheckOptions Input Format
data ConvertOptions = ConvertOptions Language Input Format Output Format PrintMode
data PrintMode = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
data PrintOptions = PrintOptions Language Input PrintMode
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
newtype ExampleOptions = ExampleOptions ExampleMode
data EraseOptions = EraseOptions Input Format Output Format PrintMode
data EvalMode = CK | CEK deriving (Show, Read)
data EvalOptions = EvalOptions Language Input Format EvalMode Timing

-- Main commands
data Command = Typecheck TypecheckOptions
             | Convert ConvertOptions
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
    <> command "convert"
           (info (Convert <$> convertoptions)
            (progDesc "Convert PLC programs between various formats"))
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
typecheckOpts = TypecheckOptions <$> input <*> inputformat

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


convertoptions :: Parser ConvertOptions
convertoptions = ConvertOptions <$> languageMode <*> input <*> inputformat <*> output <*> outputformat <*> printMode

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
evalOpts = EvalOptions <$> languageMode <*> input <*> inputformat <*> evalMode <*> timing

eraseOpts :: Parser EraseOptions
eraseOpts = EraseOptions <$> input <*> inputformat <*> output <*> outputformat <*> printMode

---------------- Name conversions ----------------

toDeBruijn :: UntypedProgram a -> IO (UntypedProgramDeBruijn a)
toDeBruijn prog = do
  r <- PLC.runQuoteT $ runExceptT (UPLC.deBruijnProgram prog)
  case r of
    Left e  -> hPutStrLn stderr (show e) >> exitFailure
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p


fromDeBruijn :: UntypedProgramDeBruijn a -> IO (UntypedProgram a)
fromDeBruijn prog = do
    let namedProgram = UPLC.programMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "v" ix) prog
    case PLC.runQuote $ runExceptT $ UPLC.unDeBruijnProgram namedProgram of
      Left e  -> hPutStrLn stderr (show e) >> exitFailure
      Right p -> return p

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
            failWith (err :: PlcParserError) =  T.hPutStrLn stderr (PP.displayPlcDef err) >> exitFailure


-- Read a CBOR-encoded PLC AST
getCborInput :: Input -> IO BSL.ByteString
getCborInput StdInput         = BSL.getContents
getCborInput (FileInput file) = BSL.readFile file


-- ### We only need deBruijn-named programs for input and output, and then only for
-- untyped PLC.  So loadASTfromCBOR and writeCBOR probably need a flag telling them to
-- do the conversion.

-- Read and deserialise a CBOR-encoded AST
loadASTfromCBOR :: Language -> CborMode -> Input -> IO (Program ())
loadASTfromCBOR language cborMode inp =
    case (language, cborMode) of
         (TypedPLC, Named)      -> getCborInput inp <&> deserialiseOrFail >>= handleResult TypedProgram
         (TypedPLC, DeBruijn)   -> hPutStrLn stderr "No CBOR for typed PLC" >> exitFailure
         (UntypedPLC, Named)    -> getCborInput inp <&> deserialiseOrFail >>= handleResult UntypedProgram
         (UntypedPLC, DeBruijn) -> getCborInput inp <&> deserialiseOrFail >>= mapM fromDeBruijn >>= handleResult UntypedProgram
    where handleResult wrapper =
              \case
               Left (DeserialiseFailure offset msg) ->
                   hPutStrLn stderr ("Deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg) >> exitFailure
               Right r -> return $ wrapper r


-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram :: Language -> Input -> Format -> IO (Program PLC.AlexPosn)
getProgram language inp fmt =
    case fmt of
      Plc  -> parsePlcInput language inp
      Cbor cborMode -> do
               prog <- loadASTfromCBOR language cborMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.


---------------- Parse and print a PLC source file ----------------

getPrintMethod :: PP.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PP.prettyPlcClassicDef
      Debug         -> PP.prettyPlcClassicDebug
      Readable      -> PP.prettyPlcReadableDef
      ReadableDebug -> PP.prettyPlcReadableDebug

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions language inp mode) =
    parsePlcInput language inp >>= print . (getPrintMethod mode)


---------------- Convert a PLC source file to CBOR ----------------

serialiseProgram :: Serialise a => Program a -> BSL.ByteString
serialiseProgram (TypedProgram p)   = serialise p
serialiseProgram (UntypedProgram p) = serialise p

writeCBOR :: Output -> CborMode -> Program a -> IO ()
writeCBOR outp cborMode prog = do
  cbor <- case cborMode of
            Named -> pure $ serialiseProgram (() <$ prog) -- Change annotations to (): see Note [Annotation types].
            DeBruijn -> case prog of
                          TypedProgram _ -> error "No CBOR for typed PLC"
                          UntypedProgram p -> do
                                dbProg <- toDeBruijn p
                                pure $ serialise (() <$ dbProg)
  case outp of
    FileOutput file -> BSL.writeFile file cbor
    StdOutput       -> BSL.putStr cbor >> T.putStrLn ""

--runPlcToCbor :: PlcToCborOptions -> IO ()
--runPlcToCbor (PlcToCborOptions language inp outp) =
--  parsePlcInput language inp >>= writeCBOR outp


---------------- Convert a CBOR file to PLC source ----------------

writePlc :: Output -> PrintMode -> Program a -> IO ()
writePlc outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog

--runCborToPlc :: CborToPlcOptions -> IO ()
--runCborToPlc (CborToPlcOptions language inp outp mode) =
--  loadASTfromCBOR language inp >>= writePlc outp mode


writeProgram :: Output -> Format -> PrintMode -> Program a -> IO ()
writeProgram outp Plc mode prog          = writePlc outp mode prog
writeProgram outp (Cbor cborMode) _ prog = writeCBOR outp cborMode prog

---------------- Conversions ----------------
runConvert :: ConvertOptions -> IO ()
runConvert (ConvertOptions lang inp ifmt outp ofmt mode) = do
    program <- getProgram lang inp ifmt
    writeProgram outp ofmt mode program


---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TermExample = TermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni ())
data SomeExample = SomeTypeExample TypeExample | SomeTermExample TermExample

prettySignature :: ExampleName -> SomeExample -> Doc ann
prettySignature name (SomeTypeExample (TypeExample kind _)) =
    pretty name <+> "::" <+> PP.prettyPlcDef kind
prettySignature name (SomeTermExample (TermExample ty _)) =
    pretty name <+> ":"  <+> PP.prettyPlcDef ty

prettyExample :: SomeExample -> Doc ann
prettyExample (SomeTypeExample (TypeExample _ ty))   = PP.prettyPlcDef ty
prettyExample (SomeTermExample (TermExample _ term)) =
    PP.prettyPlcDef $ PLC.Program () (PLC.defaultVersion ()) term

toTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni () -> TermExample
toTermExample term = TermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    ty = case PLC.runQuote . runExceptT $ PLC.typecheckPipeline PLC.defConfig program of
        Left (err :: PLC.Error PLC.DefaultUni ()) -> error $ PP.displayPlcDef err
        Right vTy                                 -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni ())]
getInteresting =
    sequence $ Gen.fromInterestingTermGens $ \name gen -> do
        Gen.TermOf term _ <- Gen.getSampleTermValue gen
        pure (T.pack name, term)

simpleExamples :: [(ExampleName, SomeExample)]
simpleExamples =
    [ ("succInteger", SomeTermExample $ toTermExample StdLib.succInteger)
    , ("unit"       , SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.unit)
    , ("unitval"    , SomeTermExample $ toTermExample StdLib.unitval)
    , ("bool"       , SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.bool)
    , ("true"       , SomeTermExample $ toTermExample StdLib.true)
    , ("false"      , SomeTermExample $ toTermExample StdLib.false)
    , ("churchNat"  , SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.churchNat)
    , ("churchZero" , SomeTermExample $ toTermExample StdLib.churchZero)
    , ("churchSucc" , SomeTermExample $ toTermExample StdLib.churchSucc)
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
    traverse_ (T.putStrLn . PP.render . uncurry prettySignature) examples
runExample (ExampleOptions (ExampleSingle name)) = do
    examples <- getAvailableExamples
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PP.render $ prettyExample ex


---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  TypedProgram prog <- getProgram TypedPLC inp fmt
  case PLC.runQuoteT $ do
    types <- PLC.getStringBuiltinTypes ()
    PLC.typecheckPipeline (PLC.TypeCheckConfig types) (void prog)
    of
       Left (e :: PLC.Error PLC.DefaultUni ()) -> T.hPutStrLn stderr (PP.displayPlcDef e) >> exitFailure
       Right ty                                -> T.putStrLn (PP.displayPlcDef ty) >> exitSuccess


---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions language inp fmt mode printtime) =
    case language of

      TypedPLC -> do
        TypedProgram prog <- getProgram TypedPLC inp fmt
        let evaluate = case mode of
                          CK  -> PLC.unsafeEvaluateCk  (PLC.getStringBuiltinMeanings @ (PLC.CkValue  PLC.DefaultUni))
                          CEK -> PLC.unsafeEvaluateCek (PLC.getStringBuiltinMeanings @ (PLC.CekValue PLC.DefaultUni)) PLC.defaultCostModel
            body = void . PLC.toTerm $ prog
        () <-  Exn.evaluate $ rnf body
        -- ^ Force evaluation of body to ensure that we're not timing parsing/deserialisation.
        -- The parser apparently returns a fully-evaluated AST, but let's be on the safe side.
        start <- performGC >> getCPUTime
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
                  () <- Exn.evaluate $ rnf body
                  start <- getCPUTime
                  case evaluate body of
                    UPLC.EvaluationSuccess v -> succeed start v
                    UPLC.EvaluationFailure   -> exitFailure

    where succeed start v = do
            end <- getCPUTime
            T.putStrLn $ PP.displayPlcDef v
            let ms = 1e9 :: Double
                diff = (fromIntegral (end - start)) / ms
            when (printtime == Timing) $ printf "Evaluation time: %0.2f ms\n" diff
            exitSuccess

---------------- Erasure ----------------

-- | Input a program, erase the types, then output it
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp ifmt outp ofmt mode) = do
  TypedProgram typedProg <- getProgram TypedPLC inp ifmt
  let untypedProg = () <$ (UntypedProgram $ UPLC.eraseProgram typedProg)
  case ofmt of
    Plc           -> writePlc outp mode untypedProg
    Cbor cborMode -> writeCBOR outp cborMode untypedProg


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
        Convert   opts -> runConvert   opts
