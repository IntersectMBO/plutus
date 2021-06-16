{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TypeApplications          #-}

module Main (main) where

import           PlutusPrelude                            (through)

import qualified PlutusCore                               as PLC
import qualified PlutusCore.CBOR                          as PLC
import           PlutusCore.Check.Uniques                 (checkProgram)
import qualified PlutusCore.Evaluation.Machine.Ck         as Ck
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..), ExRestrictingBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..), ExMemory (..))
import qualified PlutusCore.Generators                    as Gen
import qualified PlutusCore.Generators.Interesting        as Gen
import qualified PlutusCore.Generators.Test               as Gen
import qualified PlutusCore.Pretty                        as PP
import           PlutusCore.Rename                        (rename)
import qualified PlutusCore.StdLib.Data.Bool              as StdLib
import qualified PlutusCore.StdLib.Data.ChurchNat         as StdLib
import qualified PlutusCore.StdLib.Data.Integer           as StdLib
import qualified PlutusCore.StdLib.Data.Unit              as StdLib

import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import qualified Uplc.Main                                as UPLC (Program)

import           Codec.Serialise                          (DeserialiseFailure (DeserialiseFailure))
import           Control.DeepSeq                          (NFData, rnf)
import           Control.Monad                            (void)
import           Control.Monad.Trans.Except               (runExceptT)
import           Data.Bifunctor                           (second)
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Foldable                            (asum, traverse_)
import           Data.Function                            ((&))
import qualified Data.HashMap.Monoidal                    as H
import           Data.List                                (nub)
import qualified Data.List                                as List
import           Data.List.Split                          (splitOn)
import qualified Data.Text                                as T
import           Data.Text.Encoding                       (encodeUtf8)
import qualified Data.Text.IO                             as T
import           Data.Text.Prettyprint.Doc                (Doc, pretty, (<+>))
import           Data.Traversable                         (for)
import           Flat                                     (Flat, flat, unflat)
import           Options.Applicative
import           System.CPUTime                           (getCPUTime)
import           System.Exit                              (exitFailure, exitSuccess)
import           System.Mem                               (performGC)
import           Text.Printf                              (printf)
import           Text.Read                                (readMaybe)

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

type Program a = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun a

-- instance (PP.PrettyBy PP.PrettyConfigPlc (Program a)) where
    -- prettyBy cfg p   = PP.prettyBy cfg p

---------------- Types for commands and arguments ----------------

data Input       = FileInput FilePath | StdInput
data Output      = FileOutput FilePath | StdOutput
data TimingMode  = NoTiming | Timing Integer deriving (Eq)  -- Report program execution time?
data CekModel    = Default | Unit   -- Which cost model should we use for CEK machine steps?
data PrintMode   = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
data EvalMode    = CK | CEK deriving (Show, Read)
data BudgetMode  = Silent
                 | forall cost. (Eq cost, NFData cost, PrintBudgetState cost) =>
                     Verbose (Cek.ExBudgetMode cost PLC.DefaultUni PLC.DefaultFun)
-- PLC doesn't support de Bruijn indices when (de)serialising ASTs
data AstNameType = Named deriving (Show)
type Files       = [FilePath]

-- | Input/output format for programs
data Format =
  Plc
  | Cbor AstNameType
  | Flat AstNameType
  deriving (Show)

data TypecheckOptions = TypecheckOptions Input Format
data ConvertOptions   = ConvertOptions Input Format Output Format PrintMode
data PrintOptions     = PrintOptions Input PrintMode
newtype ExampleOptions   = ExampleOptions ExampleMode
data EraseOptions     = EraseOptions Input Format Output Format PrintMode
data EvalOptions      = EvalOptions Input Format EvalMode PrintMode BudgetMode TimingMode CekModel
data ApplyOptions     = ApplyOptions Files Format Output Format PrintMode

-- Main commands
data Command = Apply     ApplyOptions
             | Typecheck TypecheckOptions
             | Convert   ConvertOptions
             | Print     PrintOptions
             | Example   ExampleOptions
             | Erase     EraseOptions
             | Eval      EvalOptions


---------------- Option parsers ----------------

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

formatHelp :: String
formatHelp = "plc, cbor (de Bruijn indices), cbor-named (names), flat (de Bruijn indices), or flat-named (names)"

formatReader :: String -> Maybe Format
formatReader =
    \case
         "plc"        -> Just Plc
         "cbor-named" -> Just (Cbor Named)
         "flat-named" -> Just (Flat Named)
         _            -> Nothing

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


-- Reader for budget.  The --restricting option requires two integer arguments
-- and the easiest way to do this is to supply a colon-separated pair of
-- integers.
exbudgetReader :: ReadM ExBudget
exbudgetReader = do
  s <- str
  case splitOn ":" s of
    [a,b] -> case (readMaybe a, readMaybe b) of
               (Just cpu, Just mem) -> pure $ ExBudget (ExCPU cpu) (ExMemory mem)
               _                    -> readerError badfmt
    _     -> readerError badfmt
    where badfmt = "Invalid budget (expected eg 10000:50000)"

restrictingbudgetEnormous :: Parser BudgetMode
restrictingbudgetEnormous = flag' (Verbose Cek.restrictingEnormous)
                            (  long "restricting-enormous"
                            <> short 'r'
                            <> help "Run the machine in restricting mode with an enormous budget" )

restrictingbudget :: Parser BudgetMode
restrictingbudget = Verbose . Cek.restricting . ExRestrictingBudget
                    <$> option exbudgetReader
                            (  long "restricting"
                            <> short 'R'
                            <> metavar "ExCPU:ExMemory"
                            <> help "Run the machine in restricting mode with the given limits" )

countingbudget :: Parser BudgetMode
countingbudget = flag' (Verbose Cek.counting)
                 (  long "counting"
                 <> short 'c'
                 <> help "Run machine in counting mode and report results" )

tallyingbudget :: Parser BudgetMode
tallyingbudget = flag' (Verbose Cek.tallying)
                 (  long "tallying"
                 <> short 't'
                 <> help "Run machine in tallying mode and report results" )

budgetmode :: Parser BudgetMode
budgetmode = asum
    [ restrictingbudgetEnormous
    , restrictingbudget
    , countingbudget
    , tallyingbudget
    , pure Silent
    ]

-- -x -> run 100 times and print the mean time
timing1 :: Parser TimingMode
timing1 = flag NoTiming (Timing 100)
  (  short 'x'
  <> help "Report mean execution time of program over 100 repetitions"
  )

-- -X N -> run N times and print the mean time
timing2 :: Parser TimingMode
timing2 = Timing <$> option auto
  (  long "time-execution"
  <> short 'X'
  <> metavar "N"
  <> help "Report mean execution time of program over N repetitions. Use a large value of N if possible to get accurate results."
  )

-- We really do need two separate parsers here.
-- See https://github.com/pcapriotti/optparse-applicative/issues/194#issuecomment-205103230
timingmode :: Parser TimingMode
timingmode = timing1 <|> timing2

cekmodel :: Parser CekModel
cekmodel = flag Default Unit
           (  short '1'
           <> long "unit-cek-model"
           <> help "Use unit AST node costs for CEK cost model (tallying mode only)"
           )

files :: Parser Files
files = some (argument str (metavar "[FILES...]"))

applyOpts :: Parser ApplyOptions
applyOpts = ApplyOptions <$>  files <*> inputformat <*> output <*> outputformat <*> printmode

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> inputformat

printmode :: Parser PrintMode
printmode = option auto
  (  long "print-mode"
  <> metavar "MODE"
  <> value Classic
  <> showDefault
  <> help ("Print mode for plc output (ignored elsewhere): Classic -> plcPrettyClassicDef, Debug -> plcPrettyClassicDebug, "
        ++ "Readable -> prettyPlcReadableDef, ReadableDebug -> prettyPlcReadableDebug" ))

printOpts :: Parser PrintOptions
printOpts = PrintOptions <$> input <*> printmode

convertOpts :: Parser ConvertOptions
convertOpts = ConvertOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

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

eraseOpts :: Parser EraseOptions
eraseOpts = EraseOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

evalmode :: Parser EvalMode
evalmode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CEK
  <> showDefault
  <> help "Evaluation mode (CK or CEK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOptions <$> input <*> inputformat <*> evalmode <*> printmode <*> budgetmode <*> timingmode <*> cekmodel

helpText ::
  -- | Either "Untyped Plutus Core" or "Typed Plutus Core"
  String -> String
helpText lang =
       "This program provides a number of utilities for dealing with "
    ++ lang
    ++ "programs, including typechecking, evaluation, and conversion between a "
    ++ "number of different formats.  The program also provides a number of example "
    ++ "programs.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in CBOR or Flat format: ASTs are always written with "
    ++ "unit annotations, and any CBOR/Flat-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a serialised AST with any "
    ++ "non-unit annotation type will cause an error."

plcHelpText :: String
plcHelpText = helpText "Typed Plutus Core"

plutus ::
  -- | Either "Untyped Plutus Core Tool" or "Typed Plutus Core Tool"
  String
  -> ParserInfo Command
plutus lang = info (plutusOpts <**> helper) (fullDesc <> header lang <> progDesc plcHelpText)

plcInfoCommand :: ParserInfo Command
plcInfoCommand = plutus "Typed Plutus Core Tool"

plutusOpts :: Parser Command
plutusOpts = hsubparser (
       command "apply"
           (info (Apply <$> applyOpts)
            (progDesc $ "Given a list of input scripts f g1 g2 ... gn, output a script consisting of (... ((f g1) g2) ... gn); "
            ++ "for example, 'plc apply --if cbor Validator.cbor Datum.cbor Redeemer.cbor Context.cbor --of cbor -o Script.cbor'"))
    <> command "print"
           (info (Print <$> printOpts)
            (progDesc "Parse a program then prettyprint it."))
    <> command "convert"
           (info (Convert <$> convertOpts)
            (progDesc "Convert PLC programs between various formats"))
    <> command "example"
           (info (Example <$> exampleOpts)
            (progDesc $ "Show a typed or untyped Plutus Core program example. "
                     ++ "Usage: first request the list of available examples (optional step), "
                     ++ "then request a particular example by the name of a term (or also a "
                     ++ "type if --typed is specified). "
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

---------------- Name conversions ----------------

---------------- Reading programs from files ----------------

-- Read a PLC source program
getPlcInput :: Input -> IO String
getPlcInput (FileInput file) = readFile file
getPlcInput StdInput         = getContents

-- | Read and parse a source program
parseInput :: PLC.Rename a =>
  -- | The parseProgram function for either UPLC or PLC
  (BSL.ByteString -> PLC.QuoteT (Either (PLC.ParseError PLC.AlexPosn)) a) ->
  -- | The checkProgram function for either UPLC or PLC
  ((PLC.UniqueError ann -> Bool) -> a -> Either (PLC.UniqueError PLC.AlexPosn) ()) ->
  -- | The source program
  Input ->
  -- | The output is either a UPLC or PLC program
  IO a
parseInput parseProg checkProg inp = do
    bsContents <- BSL.fromStrict . encodeUtf8 . T.pack <$> getPlcInput inp
    -- parse the UPLC program
    case PLC.runQuoteT $ parseProg bsContents of
      -- when it's failed, pretty print parse errors.
      Left (err :: PLC.ParseError PLC.AlexPosn) ->
        errorWithoutStackTrace $ PP.render $ pretty err
      -- otherwise,
      Right p -> do
        -- run @rename@ through the program
        renamed <- PLC.runQuoteT $ rename p
        -- check the program for @UniqueError@'s
        let checked = through (checkProg (const True)) renamed
        case checked of
          -- pretty print the error
          Left (err :: PLC.UniqueError PLC.AlexPosn) ->
            errorWithoutStackTrace $ PP.render $ pretty err
          -- if there's no errors, return the parsed program
          Right _ -> pure p

parsePlcInput :: Input
  -> IO
     (PLC.Program
        PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun PLC.AlexPosn)
parsePlcInput = parseInput PLC.parseProgram checkProgram

-- Read a binary-encoded file (eg, CBOR- or Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput         = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

-- Read and deserialise a CBOR-encoded AST
loadASTfromCBOR :: Input -> IO (Program ())
loadASTfromCBOR inp = do
    bin <- getBinaryInput inp
    case PLC.deserialiseRestoringUnitsOrFail bin of
      Left (DeserialiseFailure offset msg) ->
        errorWithoutStackTrace $ "CBOR deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg
      Right r -> return r

-- Read and deserialise a Flat-encoded AST
loadASTfromFlat :: Input -> IO (Program ())
loadASTfromFlat inp = do
    bin <- getBinaryInput inp
    --  >>= handleResult TypedProgram . unflat
    case unflat bin of
      Left e  -> errorWithoutStackTrace $ "Flat deserialisation failure: " ++ show e
      Right r -> return r


-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram ::  Format -> Input  -> IO (Program PLC.AlexPosn)
getProgram fmt inp =
    case fmt of
      Plc  -> parsePlcInput inp
      Cbor _ -> do
               prog <- loadASTfromCBOR inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.
      Flat _ -> do
               prog <- loadASTfromFlat inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.


---------------- Serialise a program using CBOR ----------------

serialiseProgramCBOR :: Program () -> BSL.ByteString
serialiseProgramCBOR = PLC.serialiseOmittingUnits

writeCBOR :: Output -> Program a -> IO ()
writeCBOR outp prog = do
  let cbor = serialiseProgramCBOR (() <$ prog) -- Change annotations to (): see Note [Annotation types].
  case outp of
    FileOutput file -> BSL.writeFile file cbor
    StdOutput       -> BSL.putStr cbor

---------------- Serialise a program using Flat ----------------

serialiseProgramFlat :: Flat a => Program a -> BSL.ByteString
serialiseProgramFlat p = BSL.fromStrict $ flat p

writeFlat :: Output -> Program a -> IO ()
writeFlat outp prog = do
  let flatProg = serialiseProgramFlat (() <$ prog) -- Change annotations to (): see Note [Annotation types].
  case outp of
    FileOutput file -> BSL.writeFile file flatProg
    StdOutput       -> BSL.putStr flatProg


---------------- Write an AST as PLC source ----------------

getPrintMethod :: PP.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PP.prettyPlcClassicDef
      Debug         -> PP.prettyPlcClassicDebug
      Readable      -> PP.prettyPlcReadableDef
      ReadableDebug -> PP.prettyPlcReadableDebug

-- | Print out a PLC program in IO.
writePlc :: Output -> PrintMode -> Program a -> IO ()
writePlc outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog

-- | Print out a UPLC program to IO.
writeUplc :: Output -> PrintMode -> UPLC.Program a -> IO ()
writeUplc outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog

writeProgram :: Output -> Format -> PrintMode -> Program a -> IO ()
writeProgram outp Plc mode prog   = writePlc outp mode prog
writeProgram outp (Cbor _) _ prog = writeCBOR outp prog
writeProgram outp (Flat _) _ prog = writeFlat outp prog


---------------- Conversions ----------------

-- | Convert between textual and CBOR representations.  This subsumes the
-- `print` command: for example, `plc convert -i prog.plc --typed --fmt Readable`
-- will read a typed plc file and print it in the Readable format.  Having
-- the separate `print` option may be more user-friendly though.
runConvert :: ConvertOptions -> IO ()
runConvert (ConvertOptions inp ifmt outp ofmt mode) = do
    program <- getProgram ifmt inp
    writeProgram outp ofmt mode program


---------------- Parse and print a PLC source file ----------------

runPrint ::
  (Input
  -> IO
     (PLC.Program
        PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun PLC.AlexPosn)) ->
  PrintOptions -> IO ()
runPrint parseFn (PrintOptions inp mode) =
    parseFn inp >>= print . getPrintMethod mode

runPlcPrint :: PrintOptions -> IO ()
runPlcPrint = runPrint parsePlcInput

---------------- Erasure ----------------

-- | Input a program, erase the types, then output it
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp ifmt outp ofmt mode) = do
  typedProg <- getProgram ifmt inp
  let untypedProg = () <$ UPLC.eraseProgram typedProg
  case ofmt of
    Plc    -> writeUplc outp mode untypedProg
    Cbor _ -> writeCBOR outp untypedProg
    Flat _ -> writeFlat outp untypedProg


---------------- Script application ----------------

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM (getProgram ifmt . FileInput) inputfiles
  let appliedScript =
        case map (\case p -> () <$ p) scripts of
          []          -> errorWithoutStackTrace "No input files"
          progAndargs -> foldl1 PLC.applyProgram progAndargs
  writeProgram outp ofmt mode appliedScript

---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TypedTermExample = TypedTermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())
data SomeTypedExample = SomeTypeExample TypeExample | SomeTypedTermExample TypedTermExample

newtype UntypedTermExample = UntypedTermExample
    (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
newtype SomeUntypedExample = SomeUntypedTermExample UntypedTermExample

data SomeExample = SomeTypedExample SomeTypedExample | SomeUntypedExample SomeUntypedExample

prettySignature :: ExampleName -> SomeExample -> Doc ann
prettySignature name (SomeTypedExample (SomeTypeExample (TypeExample kind _))) =
    pretty name <+> "::" <+> PP.prettyPlcDef kind
prettySignature name (SomeTypedExample (SomeTypedTermExample (TypedTermExample ty _))) =
    pretty name <+> ":"  <+> PP.prettyPlcDef ty
prettySignature name (SomeUntypedExample _) =
    pretty name

prettyExample :: SomeExample -> Doc ann
prettyExample =
    \case
         SomeTypedExample (SomeTypeExample (TypeExample _ ty)) -> PP.prettyPlcDef ty
         SomeTypedExample (SomeTypedTermExample (TypedTermExample _ term))
             -> PP.prettyPlcDef $ PLC.Program () (PLC.defaultVersion ()) term
         SomeUntypedExample (SomeUntypedTermExample (UntypedTermExample term)) ->
             PP.prettyPlcDef $ UPLC.Program () (PLC.defaultVersion ()) term

toTypedTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun () -> TypedTermExample
toTypedTermExample term = TypedTermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    errOrTy = PLC.runQuote . runExceptT $ do
        tcConfig <- PLC.getDefTypeCheckConfig ()
        PLC.typecheckPipeline tcConfig program
    ty = case errOrTy of
        Left (err :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) -> errorWithoutStackTrace $ PP.displayPlcDef err
        Right vTy                                                -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())]
getInteresting =
    sequence $ Gen.fromInterestingTermGens $ \name gen -> do
        Gen.TermOf term _ <- Gen.getSampleTermValue gen
        pure (T.pack name, term)

simpleExamples :: [(ExampleName, SomeTypedExample)]
simpleExamples =
    [ ("succInteger", SomeTypedTermExample $ toTypedTermExample StdLib.succInteger)
    , ("unit"       , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.unit)
    , ("unitval"    , SomeTypedTermExample $ toTypedTermExample StdLib.unitval)
    , ("bool"       , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.bool)
    , ("true"       , SomeTypedTermExample $ toTypedTermExample StdLib.true)
    , ("false"      , SomeTypedTermExample $ toTypedTermExample StdLib.false)
    , ("churchNat"  , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.churchNat)
    , ("churchZero" , SomeTypedTermExample $ toTypedTermExample StdLib.churchZero)
    , ("churchSucc" , SomeTypedTermExample $ toTypedTermExample StdLib.churchSucc)
    ]


-- TODO: This supplies both typed and untyped examples.  Currently the untyped
-- examples are obtained by erasing typed ones, but it might be useful to have
-- some untyped ones that can't be obtained by erasure.
getAvailableExamples :: IO [(ExampleName, SomeExample)]
getAvailableExamples = do
    interesting <- getInteresting
    let examples = simpleExamples ++ map (second $ SomeTypedTermExample . toTypedTermExample) interesting
    pure $ map (fmap SomeTypedExample) examples

-- The implementation is a little hacky: we generate interesting examples when the list of examples
-- is requested and at each lookup of a particular example. I.e. each time we generate distinct
-- terms. But types of those terms must not change across requests, so we're safe.

runPrintExample :: ExampleOptions -> IO ()
runPrintExample (ExampleOptions ExampleAvailable) = do
    examples <- getAvailableExamples
    traverse_ (T.putStrLn . PP.render . uncurry prettySignature) examples
runPrintExample (ExampleOptions (ExampleSingle name)) = do
    examples <- getAvailableExamples
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PP.render $ prettyExample ex


---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  prog <- getProgram fmt inp
  case PLC.runQuoteT $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.typecheckPipeline tcConfig (void prog)
    of
      Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
        errorWithoutStackTrace $ PP.displayPlcDef e
      Right ty                                               ->
        T.putStrLn (PP.displayPlcDef ty) >> exitSuccess


---------------- Timing ----------------

-- Convert a time in picoseconds into a readble format with appropriate units
formatTimePicoseconds :: Double -> String
formatTimePicoseconds t
    | t >= 1e12 = printf "%.3f s"  (t/1e12)
    | t >= 1e9  = printf "%.3f ms" (t/1e9)
    | t >= 1e6  = printf "%.3f μs" (t/1e6)
    | t >= 1e3  = printf "%.3f ns" (t/1e3)
    | otherwise = printf "%f ps"   t

{-| Apply an evaluator to a program a number of times and report the mean execution
time.  The first measurement is often significantly larger than the rest
(perhaps due to warm-up effects), and this can distort the mean.  To avoid this
we measure the evaluation time (n+1) times and discard the first result. -}
timeEval :: NFData a => Integer -> (t -> a) -> t -> IO [a]
timeEval n evaluate prog
    | n <= 0 = errorWithoutStackTrace "Error: the number of repetitions should be at least 1"
    | otherwise = do
  (results, times) <- unzip . tail <$> for (replicate (fromIntegral (n+1)) prog) (timeOnce evaluate)
  let mean = fromIntegral (sum times) / fromIntegral n :: Double
      runs :: String = if n==1 then "run" else "runs"
  printf "Mean evaluation time (%d %s): %s\n" n runs (formatTimePicoseconds mean)
  pure results
    where timeOnce eval prg = do
            start <- performGC >> getCPUTime
            let result = eval prg
                !_ = rnf result
            end <- getCPUTime
            pure (result, end - start)


---------------- Printing budgets and costs ----------------

printBudgetStateBudget :: UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun () -> CekModel -> ExBudget -> IO ()
printBudgetStateBudget _ model b =
    case model of
      Unit -> pure ()
      _ ->  let ExCPU cpu = _exBudgetCPU b
                ExMemory mem = _exBudgetMemory b
            in do
              putStrLn $ "CPU budget:    " ++ show cpu
              putStrLn $ "Memory budget: " ++ show mem

printBudgetStateTally :: (Eq fun, Cek.Hashable fun, Show fun)
       => UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun () -> CekModel ->  Cek.CekExTally fun -> IO ()
printBudgetStateTally term model (Cek.CekExTally costs) = do
  putStrLn $ "Const      " ++ pbudget (Cek.BStep Cek.BConst)
  putStrLn $ "Var        " ++ pbudget (Cek.BStep Cek.BVar)
  putStrLn $ "LamAbs     " ++ pbudget (Cek.BStep Cek.BLamAbs)
  putStrLn $ "Apply      " ++ pbudget (Cek.BStep Cek.BApply)
  putStrLn $ "Delay      " ++ pbudget (Cek.BStep Cek.BDelay)
  putStrLn $ "Force      " ++ pbudget (Cek.BStep Cek.BForce)
  putStrLn $ "Builtin    " ++ pbudget (Cek.BStep Cek.BBuiltin)
  putStrLn ""
  putStrLn $ "startup    " ++ pbudget Cek.BStartup
  putStrLn $ "compute    " ++ printf "%-20s" (budgetToString totalComputeCost)
  putStrLn $ "AST nodes  " ++ printf "%15d" (UPLC.termSize term)
  putStrLn ""
  putStrLn $ "BuiltinApp " ++ budgetToString builtinCosts
  case model of
    Default ->
        do
  -- 1e9*(0.200  + 0.0000725 * totalComputeSteps + builtinExeTimes/1000)  putStrLn ""
          putStrLn ""
          traverse_ (\(b,cost) -> putStrLn $ printf "%-20s %s" (show b) (budgetToString cost :: String)) builtinsAndCosts
          putStrLn ""
          putStrLn $ "Total budget spent: " ++ printf (budgetToString totalCost)
          putStrLn $ "Predicted execution time: " ++ formatTimePicoseconds totalTime
    Unit -> pure ()
  where
        getSpent k =
            case H.lookup k costs of
              Just v  -> v
              Nothing -> ExBudget 0 0
        allNodeTags = fmap Cek.BStep [Cek.BConst, Cek.BVar, Cek.BLamAbs, Cek.BApply, Cek.BDelay, Cek.BForce, Cek.BBuiltin]
        totalComputeCost = mconcat $ map getSpent allNodeTags  -- For unitCekCosts this will be the total number of compute steps
        budgetToString (ExBudget (ExCPU cpu) (ExMemory mem)) =
            printf "%15s  %15s" (show cpu) (show mem) :: String -- Not %d: doesn't work when CostingInteger is SatInt.
        pbudget = budgetToString . getSpent
        f l e = case e of {(Cek.BBuiltinApp b, cost)  -> (b,cost):l; _ -> l}
        builtinsAndCosts = List.foldl f [] (H.toList costs)
        builtinCosts = mconcat (map snd builtinsAndCosts)
        -- ^ Total builtin evaluation time (according to the models) in picoseconds (units depend on BuiltinCostModel.costMultiplier)
        getCPU b = let ExCPU b' = _exBudgetCPU b in fromIntegral b'::Double
        totalCost = getSpent Cek.BStartup <> totalComputeCost <> builtinCosts
        totalTime = getCPU (getSpent Cek.BStartup) + getCPU totalComputeCost + getCPU builtinCosts

class PrintBudgetState cost where
    printBudgetState :: UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun () -> CekModel -> cost -> IO ()
    -- TODO: Tidy this up.  We're passing in the term and the CEK cost model
    -- here, but we only need them in tallying mode (where we need the term so
    -- we can print out the AST size and we need the model type to decide how
    -- much information we're going to print out).

instance PrintBudgetState Cek.CountingSt where
    printBudgetState term model (Cek.CountingSt budget) = printBudgetStateBudget term model budget

instance (Eq fun, Cek.Hashable fun, Show fun) => PrintBudgetState (Cek.TallyingSt fun) where
    printBudgetState term model (Cek.TallyingSt tally budget) = do
        printBudgetStateBudget term model budget
        putStrLn ""
        printBudgetStateTally term model tally

instance PrintBudgetState Cek.RestrictingSt where
    printBudgetState term model (Cek.RestrictingSt (ExRestrictingBudget budget)) =
        printBudgetStateBudget term model budget


---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt evalMode printMode budgetMode timingMode _) =
  case evalMode of
      CEK -> errorWithoutStackTrace "There is no CEK machine for Typed Plutus Core"
      CK  -> do
              let !_ = case budgetMode of
                          Silent    -> ()
                          Verbose _ -> errorWithoutStackTrace "There is no budgeting for typed Plutus Core"
              prog <- getProgram ifmt inp
              let evaluate = Ck.evaluateCkNoEmit PLC.defaultBuiltinsRuntime
                  term = void . PLC.toTerm $ prog
                  !_ = rnf term
                  -- Force evaluation of body to ensure that we're not timing parsing/deserialisation.
                  -- The parser apparently returns a fully-evaluated AST, but let's be on the safe side.
              case timingMode of
                NoTiming -> evaluate term & handleResult
                Timing n -> timeEval n evaluate term >>= handleTimingResults term
    where handleResult result =
              case result of
                Right v  -> print (getPrintMethod printMode v) >> exitSuccess
                Left err -> print err *> exitFailure
          handleTimingResults _ results =
              case nub results of
                [Right _]  -> exitSuccess -- We don't want to see the result here
                [Left err] -> print err >> exitFailure
                _          -> error "Timing evaluations returned inconsistent results" -- Should never happen


---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plcInfoCommand
    case options of
        Apply     opts -> runApply        opts
        Typecheck opts -> runTypecheck    opts
        Eval      opts -> runEval         opts
        Example   opts -> runPrintExample opts
        Erase     opts -> runErase        opts
        Print     opts -> runPlcPrint        opts
        Convert   opts -> runConvert      opts
