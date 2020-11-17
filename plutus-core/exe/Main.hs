{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}

module Main (main) where

import qualified Language.PlutusCore                               as PLC
-- import qualified Language.PlutusCore.CBOR                          as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Cek        as PLC
import qualified Language.PlutusCore.Evaluation.Machine.Ck         as PLC
import qualified Language.PlutusCore.Generators                    as Gen
import qualified Language.PlutusCore.Generators.Interesting        as Gen
import qualified Language.PlutusCore.Generators.Test               as Gen
import qualified Language.PlutusCore.Pretty                        as PP
import qualified Language.PlutusCore.StdLib.Data.Bool              as StdLib
import qualified Language.PlutusCore.StdLib.Data.ChurchNat         as StdLib
import qualified Language.PlutusCore.StdLib.Data.Integer           as StdLib
import qualified Language.PlutusCore.StdLib.Data.Unit              as StdLib
import qualified Language.UntypedPlutusCore                        as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn               as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

-- import           Codec.Serialise
import           Control.DeepSeq                                   (rnf)
import qualified Control.Exception                                 as Exn (evaluate)
import           Control.Monad
import           Control.Monad.Trans.Except                        (runExceptT)
import           Data.Bifunctor                                    (second)
import qualified Data.ByteString.Lazy                              as BSL
import           Data.Foldable                                     (traverse_)
import           Data.Functor                                      ((<&>))
import qualified Data.Text                                         as T
import           Data.Text.Encoding                                (encodeUtf8)
import qualified Data.Text.IO                                      as T
import           Data.Text.Prettyprint.Doc                         (Doc, pretty, (<+>))
import           Flat
import           Options.Applicative
import           System.CPUTime                                    (getCPUTime)
import           System.Exit                                       (exitFailure, exitSuccess)
import           System.IO
import           System.Mem                                        (performGC)
import           Text.Printf                                       (printf)

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
type TypedProgram a = PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun a
type UntypedProgram a = UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun a

data Program a =
      TypedProgram (TypedProgram a)
    | UntypedProgram (UntypedProgram a)
    deriving (Functor)

instance (PP.PrettyBy PP.PrettyConfigPlc (Program a)) where
    prettyBy cfg (TypedProgram p)   = PP.prettyBy cfg p
    prettyBy cfg (UntypedProgram p) = PP.prettyBy cfg p

-- | Untyped AST with names consisting solely of De Bruijn indices. This is
-- currently only used for intermediate values during CBOR/Flat
-- serialisation/deserialisation.  We may wish to add TypedProgramDeBruijn as
-- well if we modify the CEK machine to run directly on de Bruijnified ASTs, but
-- support for this is lacking elsewhere at the moment.
type UntypedProgramDeBruijn a = UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun a

type PlcParserError = PLC.Error PLC.DefaultUni PLC.DefaultFun PLC.AlexPosn


---------------- Types for commands and arguments ----------------

data Input       = FileInput FilePath | StdInput
data Output      = FileOutput FilePath | StdOutput
data Language    = TypedPLC | UntypedPLC
data Timing      = NoTiming | Timing deriving (Eq)  -- Report program execution time?
data PrintMode   = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
data EvalMode    = CK | CEK deriving (Show, Read)
data AstNameType = Named | DeBruijn  -- Do we use Names or de Bruijn indices when (de)serialising ASTs?
type Files       = [FilePath]

data Format = Plc | {-Cbor AstNameType | -} Flat AstNameType -- Input/output format for programs
instance Show Format where
    show Plc             = "plc"
    -- show (Cbor Named)    = "cbor-named"
    -- show (Cbor DeBruijn) = "cbor-deBruijn"
    show (Flat Named)    = "flat-named"
    show (Flat DeBruijn) = "flat-deBruijn"

data TypecheckOptions = TypecheckOptions Input Format
data ConvertOptions   = ConvertOptions Language Input Format Output Format PrintMode
data PrintOptions     = PrintOptions Language Input PrintMode
data ExampleOptions   = ExampleOptions ExampleMode
data EraseOptions     = EraseOptions Input Format Output Format PrintMode
data EvalOptions      = EvalOptions Language Input Format EvalMode PrintMode Timing
data ApplyOptions     = ApplyOptions Language Files Format Output Format PrintMode

-- Main commands
data Command = Apply     ApplyOptions
             | Typecheck TypecheckOptions
             | Convert   ConvertOptions
             | Print     PrintOptions
             | Example   ExampleOptions
             | Erase     EraseOptions
             | Eval      EvalOptions


---------------- Option parsers ----------------

typedPLC :: Parser Language
typedPLC = flag UntypedPLC TypedPLC (long "typed" <> short 't' <> help "Use typed Plutus Core")

untypedPLC :: Parser Language
untypedPLC = flag UntypedPLC UntypedPLC (long "untyped" <> short 'u' <> help "Use untyped Plutus Core (default)")
-- ^ NB: default is always UntypedPLC

languageMode :: Parser Language
languageMode = typedPLC <|> untypedPLC

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
         "plc"           -> Just Plc
         -- "cbor-named"    -> Just (Cbor Named)
         -- "cbor"          -> Just (Cbor DeBruijn)
         -- "cbor-deBruijn" -> Just (Cbor DeBruijn)
         "flat-named"    -> Just (Flat Named)
         "flat"          -> Just (Flat DeBruijn)
         "flat-deBruijn" -> Just (Flat DeBruijn)
         _               -> Nothing

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

timing :: Parser Timing
timing = flag NoTiming Timing
  ( long "time-execution"
  <> short 'x'
  <> help "Report execution time of program"
  )

files :: Parser Files
files = some (argument str (metavar "[FILES...]"))

applyOpts :: Parser ApplyOptions
applyOpts = ApplyOptions <$> languageMode <*> files <*> inputformat <*> output <*> outputformat <*> printmode

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
printOpts = PrintOptions <$> languageMode <*> input <*> printmode

convertOpts :: Parser ConvertOptions
convertOpts = ConvertOptions <$> languageMode <*> input <*> inputformat <*> output <*> outputformat <*> printmode

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
evalOpts = EvalOptions <$> languageMode <*> input <*> inputformat <*> evalmode <*> printmode <*> timing

helpText :: String
helpText =
       "This program provides a number of utilities for dealing with Plutus Core "
    ++ "programs, including typechecking, evaluation, and conversion between a "
    ++ "number of differnt formats.  The program also provides a number of example "
    ++ "typed Plutus Core programs.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in CBOR or Flat format: ASTs are always written with "
    ++ "unit annotations, and any CBOR/Flat-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a serialised AST with any "
    ++ "non-unit annotation type will cause an error."

plutus :: ParserInfo Command
plutus = info (plutusOpts <**> helper) (fullDesc <> header "Plutus Core tool" <> progDesc helpText)

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


---------------- Name conversions ----------------

-- We don't support de Bruijn names for typed programs because we really only
-- want serialisation for on-chain programs (and some of the functionality we'd
-- need isn't available anyway).
typedDeBruijnNotSupportedError :: IO a
typedDeBruijnNotSupportedError =
    hPutStrLn stderr "De-Bruijn-named ASTs are not supported for typed Plutus Core" >> exitFailure

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijn :: UntypedProgram a -> IO (UntypedProgramDeBruijn a)
toDeBruijn prog = do
  r <- PLC.runQuoteT $ runExceptT (UPLC.deBruijnProgram prog)
  case r of
    Left e  -> hPutStrLn stderr (show e) >> exitFailure
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p


-- | Convert an untyped de-Bruijn-indexed program to one with standard names.
-- We have nothing to base the names on, so every variable is named "v" (but
-- with a Unique for disambiguation).  Again, we don't support typed programs.
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

-- Read a binary-encoded file (eg, CBOR- or Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput         = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

-- Read and deserialise a CBOR-encoded AST
-- There's no (un-)deBruijnifier for typed PLC, so we don't handle that case.
-- loadASTfromCBOR :: Language -> AstNameType -> Input -> IO (Program ())
-- loadASTfromCBOR language cborMode inp =
--     case (language, cborMode) of
--          (TypedPLC,   Named)    -> getBinaryInput inp <&> PLC.deserialiseRestoringUnitsOrFail >>= handleResult TypedProgram
--          (UntypedPLC, Named)    -> getBinaryInput inp <&> UPLC.deserialiseRestoringUnitsOrFail >>= handleResult UntypedProgram
--          (TypedPLC,   DeBruijn) -> typedDeBruijnNotSupportedError
--          (UntypedPLC, DeBruijn) -> getBinaryInput inp <&> UPLC.deserialiseRestoringUnitsOrFail >>=
--                                    mapM fromDeBruijn >>= handleResult UntypedProgram
--     where handleResult wrapper =
--               \case
--                Left (DeserialiseFailure offset msg) ->
--                    hPutStrLn stderr ("CBOR deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg) >> exitFailure
--                Right r -> return $ wrapper r

-- Read and deserialise a Flat-encoded AST
loadASTfromFlat :: Language -> AstNameType -> Input -> IO (Program ())
loadASTfromFlat language flatMode inp =
    case (language, flatMode) of
         (TypedPLC,   Named)    -> getBinaryInput inp <&> unflat >>= handleResult TypedProgram
         (UntypedPLC, Named)    -> getBinaryInput inp <&> unflat >>= handleResult UntypedProgram
         (TypedPLC,   DeBruijn) -> typedDeBruijnNotSupportedError
         (UntypedPLC, DeBruijn) -> getBinaryInput inp <&> unflat >>= mapM fromDeBruijn >>= handleResult UntypedProgram
    where handleResult wrapper =
              \case
               Left e  -> hPutStrLn stderr ("Flat deserialisation failure:" ++ show e)  >> exitFailure
               Right r -> return $ wrapper r


-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram :: Language -> Format -> Input  -> IO (Program PLC.AlexPosn)
getProgram language fmt inp =
    case fmt of
      Plc  -> parsePlcInput language inp
      -- Cbor cborMode -> do
      --          prog <- loadASTfromCBOR language cborMode inp
      --          return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.
      Flat flatMode -> do
               prog <- loadASTfromFlat language flatMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.


---------------- Serialise a program using CBOR ----------------

-- serialiseProgramCBOR :: Program () -> BSL.ByteString
-- serialiseProgramCBOR (TypedProgram p)   = PLC.serialiseOmittingUnits p
-- serialiseProgramCBOR (UntypedProgram p) = UPLC.serialiseOmittingUnits p

-- -- | Convert names to de Bruijn indices and then serialise
-- serialiseDbProgramCBOR :: Program () -> IO (BSL.ByteString)
-- serialiseDbProgramCBOR (TypedProgram _)   = typedDeBruijnNotSupportedError
-- serialiseDbProgramCBOR (UntypedProgram p) = UPLC.serialiseOmittingUnits <$> toDeBruijn p

-- writeCBOR :: Output -> AstNameType -> Program a -> IO ()
-- writeCBOR outp cborMode prog = do
--   cbor <- case cborMode of
--             Named    -> pure $ serialiseProgramCBOR (() <$ prog) -- Change annotations to (): see Note [Annotation types].
--             DeBruijn -> serialiseDbProgramCBOR (() <$ prog)
--   case outp of
--     FileOutput file -> BSL.writeFile file cbor
--     StdOutput       -> BSL.putStr cbor >> T.putStrLn ""

---------------- Serialise a program using Flat ----------------

serialiseProgramFlat :: Flat a => Program a -> BSL.ByteString
serialiseProgramFlat (TypedProgram p)   = BSL.fromStrict $ flat p
serialiseProgramFlat (UntypedProgram p) = BSL.fromStrict $ flat p

-- | Convert names to de Bruijn indices and then serialise
serialiseDbProgramFlat :: Flat a => Program a -> IO (BSL.ByteString)
serialiseDbProgramFlat (TypedProgram _)   = typedDeBruijnNotSupportedError
serialiseDbProgramFlat (UntypedProgram p) = BSL.fromStrict . flat <$> toDeBruijn p

writeFlat :: Output -> AstNameType -> Program a -> IO ()
writeFlat outp flatMode prog = do
  flatProg <- case flatMode of
            Named    -> pure $ serialiseProgramFlat (() <$ prog) -- Change annotations to (): see Note [Annotation types].
            DeBruijn -> serialiseDbProgramFlat (() <$ prog)
  case outp of
    FileOutput file -> BSL.writeFile file flatProg
    StdOutput       -> BSL.putStr flatProg >> T.putStrLn ""  -- FIXME: no newline


---------------- Write an AST as PLC source ----------------

getPrintMethod :: PP.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PP.prettyPlcClassicDef
      Debug         -> PP.prettyPlcClassicDebug
      Readable      -> PP.prettyPlcReadableDef
      ReadableDebug -> PP.prettyPlcReadableDebug

writePlc :: Output -> PrintMode -> Program a -> IO ()
writePlc outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog

writeProgram :: Output -> Format -> PrintMode -> Program a -> IO ()
writeProgram outp Plc mode prog          = writePlc outp mode prog
-- writeProgram outp (Cbor cborMode) _ prog = writeCBOR outp cborMode prog
writeProgram outp (Flat flatMode) _ prog = writeFlat outp flatMode prog


---------------- Conversions ----------------

-- | Convert between textual and CBOR representations.  This subsumes the
-- `print` command: for example, `plc convert -i prog.plc -t --fmt Readable`
-- will read a typed plc file and print it in the Readable format.  Having
-- the separate `print` option may be more user-friendly though.
runConvert :: ConvertOptions -> IO ()
runConvert (ConvertOptions lang inp ifmt outp ofmt mode) = do
    program <- getProgram lang ifmt inp
    writeProgram outp ofmt mode program


---------------- Parse and print a PLC source file ----------------

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions language inp mode) =
    parsePlcInput language inp >>= print . (getPrintMethod mode)


---------------- Script application ----------------


-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions language inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM (getProgram language ifmt) (map FileInput inputfiles)
  let appliedScript =
          case language of  -- Annoyingly, we've got a list which could in principle contain both typed and untyped programs
            TypedPLC ->
                case map (\case TypedProgram p -> () <$ p;  _ -> error "unexpected program type mismatch") scripts of
                  []          -> error "No input files"
                  progAndargs -> TypedProgram $ foldl1 PLC.applyProgram progAndargs
            UntypedPLC ->
                case map (\case UntypedProgram p -> () <$ p; _ -> error "unexpected program type mismatch") scripts of
                  []          -> error "No input files"
                  progAndArgs -> UntypedProgram $ foldl1 UPLC.applyProgram progAndArgs
  writeProgram outp ofmt mode appliedScript


---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TermExample = TermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())
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

toTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun () -> TermExample
toTermExample term = TermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    errOrTy = PLC.runQuote . runExceptT $ do
        tcConfig <- PLC.getDefTypeCheckConfig ()
        PLC.typecheckPipeline tcConfig program
    ty = case errOrTy of
        Left (err :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) -> error $ PP.displayPlcDef err
        Right vTy                                                -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())]
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
  TypedProgram prog <- getProgram TypedPLC fmt inp
  case PLC.runQuoteT $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.typecheckPipeline tcConfig (void prog)
    of
      Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
        T.hPutStrLn stderr (PP.displayPlcDef e) >> exitFailure
      Right ty                                               ->
        T.putStrLn (PP.displayPlcDef ty) >> exitSuccess


---------------- Erasure ----------------

-- | Input a program, erase the types, then output it
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp ifmt outp ofmt mode) = do
  TypedProgram typedProg <- getProgram TypedPLC ifmt inp
  let untypedProg = () <$ (UntypedProgram $ UPLC.eraseProgram typedProg)
  case ofmt of
    Plc           -> writePlc outp mode untypedProg
    -- Cbor cborMode -> writeCBOR outp cborMode untypedProg
    Flat flatMode -> writeFlat outp flatMode untypedProg


---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions language inp ifmt evalMode printMode printtime) =
    case language of

      TypedPLC -> do
        TypedProgram prog <- getProgram TypedPLC ifmt inp
        let evaluate =
                case evalMode of
                  CK  -> PLC.unsafeEvaluateCk  PLC.defBuiltinsRuntime
                  CEK -> PLC.unsafeEvaluateCek PLC.defBuiltinsRuntime
            body = void . PLC.toTerm $ prog
        () <-  Exn.evaluate $ rnf body
        -- ^ Force evaluation of body to ensure that we're not timing parsing/deserialisation.
        -- The parser apparently returns a fully-evaluated AST, but let's be on the safe side.
        start <- performGC >> getCPUTime
        case evaluate body of
              PLC.EvaluationSuccess v -> succeed start v
              PLC.EvaluationFailure   -> exitFailure

      UntypedPLC ->
          case evalMode of
            CK  -> hPutStrLn stderr "There is no CK machine for UntypedPLC Plutus Core" >> exitFailure
            CEK -> do
                  UntypedProgram prog <- getProgram UntypedPLC ifmt inp
                  let evaluate = UPLC.unsafeEvaluateCek PLC.defBuiltinsRuntime
                      body = void . UPLC.toTerm $ prog
                  () <- Exn.evaluate $ rnf body
                  start <- getCPUTime
                  case evaluate body of
                    UPLC.EvaluationSuccess v -> succeed start v
                    UPLC.EvaluationFailure   -> exitFailure

    where succeed start v = do
            end <- getCPUTime
            print $ getPrintMethod printMode v
            let ms = 1e9 :: Double
                diff = (fromIntegral (end - start)) / ms
            when (printtime == Timing) $ printf "Evaluation time: %0.2f ms\n" diff
            exitSuccess


---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plutus
    case options of
        Apply     opts -> runApply     opts
        Typecheck opts -> runTypecheck opts
        Eval      opts -> runEval      opts
        Example   opts -> runExample   opts
        Erase     opts -> runErase     opts
        Print     opts -> runPrint     opts
        Convert   opts -> runConvert   opts
