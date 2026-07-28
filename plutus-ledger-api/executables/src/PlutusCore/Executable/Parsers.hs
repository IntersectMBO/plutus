{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Common option parsers for executables
module PlutusCore.Executable.Parsers where

import PlutusCore.AstSize (AstSize (..))
import PlutusCore.Default (BuiltinSemanticsVariant (..), DefaultFun)
import PlutusCore.Executable.Types
import UntypedPlutusCore qualified as UPLC

import Control.Lens ((^.))
import Data.List (intercalate)
import Data.Maybe
import Options.Applicative
import System.FilePath (takeExtension)

{-| Parser for an input stream. If none is specified,
default to stdin for ease of use in pipeline. -}
input :: Parser Input
input = fileInput <|> stdInput <|> pure StdInput

fileInput :: Parser Input
fileInput =
  FileInput
    <$> strOption
      ( long "input"
          <> short 'i'
          <> metavar "FILENAME"
          <> action "file"
          <> help "Input file"
      )

stdInput :: Parser Input
stdInput =
  flag'
    StdInput
    ( long "stdin"
        <> help "Read from stdin (default)"
    )

{-| Parser for an output stream. If none is specified,
default to stdout for ease of use in pipeline. -}
output :: Parser Output
output = fileOutput <|> stdOutput <|> noOutput <|> pure StdOutput

fileOutput :: Parser Output
fileOutput =
  FileOutput
    <$> strOption
      ( long "output"
          <> short 'o'
          <> metavar "FILENAME"
          <> action "file"
          <> help "Output file"
      )

stdOutput :: Parser Output
stdOutput =
  flag'
    StdOutput
    ( long "stdout"
        <> help "Write to stdout (default)"
    )

noOutput :: Parser Output
noOutput =
  flag'
    NoOutput
    ( long "silent"
        <> short 's'
        <> help "Don't output the evaluation result"
    )

-- Reverse lookup in a name/value option table for 'showDefaultWith', so the
-- displayed default is exactly a string the option's reader accepts. Keyed on
-- 'show' rather than value equality because not every option value type has
-- an 'Eq' instance.
showByTable :: Show a => [(String, a)] -> a -> String
showByTable table v = fromMaybe "" $ lookup (show v) [(show v', name) | (name, v') <- table]

-- The single source of truth for each format's name, description (shown in
-- --help), and value; the reader and shell completion are derived from it.
formatTable :: [(String, Maybe String, Format)]
formatTable =
  [ ("textual", Nothing, Textual)
  , ("serialised", Just "cbor + flat, with de Bruijn indices", Serialised)
  , ("hex", Just "hex + cbor + flat", Hex)
  , ("flat-named", Just "names", Flat Named)
  , ("flat", Just "de Bruijn indices", Flat DeBruijn)
  , ("flat-deBruijn", Just "alias for flat", Flat DeBruijn)
  , ("flat-namedDeBruijn", Just "names and de Bruijn indices", Flat NamedDeBruijn)
  , ("blueprint", Nothing, Blueprint)
  ]

formatHelp :: String
formatHelp =
  intercalate
    ", "
    [maybe name (\d -> name <> " (" <> d <> ")") mdesc | (name, mdesc, _) <- formatTable]

formatReader :: String -> Maybe Format
formatReader s = listToMaybe [v | (name, _, v) <- formatTable, name == s]

formatNames :: [String]
formatNames = [name | (name, _, _) <- formatTable]

inputformat :: Parser Format
inputformat =
  option
    (maybeReader formatReader)
    ( long "if"
        <> long "input-format"
        <> metavar "FORMAT"
        <> value Textual
        <> showDefault
        <> completeWith formatNames
        <> help ("Input format: " ++ formatHelp)
    )

-- File extensions that imply a non-textual format, common to every language
-- (UPLC, PLC, PIR all share the same flat/hex/cbor conventions).
nonTextualExtensionTable :: [(String, Format)]
nonTextualExtensionTable =
  [ (".flat", Flat DeBruijn)
  , (".hex", Hex)
  , (".cbor", Serialised)
  ]

{-| Guess the format from a file name's extension, given the extension that
denotes /this/ language's own textual format (@.uplc@ for UPLC, @.plc@ for
PLC). Returns 'Nothing' for an unrecognised extension, in which case callers
fall back to 'Textual'. -}
formatFromExtension :: String -> FilePath -> Maybe Format
formatFromExtension textualExt path
  | takeExtension path == textualExt = Just Textual
  | otherwise = lookup (takeExtension path) nonTextualExtensionTable

{-| Describe, for the @--if@/@--of@ help text, which extensions are deduced to
which format for this language's @textualExt@, restricted to the formats in
the given table (an extension whose format isn't in @table@ is omitted, since
it falls back to textual instead). -}
extensionHelp :: String -> [(String, Maybe String, Format)] -> String
extensionHelp textualExt table =
  intercalate ", " (mapMaybe describe ((textualExt, Textual) : nonTextualExtensionTable))
  where
    describe (ext, fmt) =
      (\name -> ext <> " -> " <> name) <$> listToMaybe [name | (name, _, fmt') <- table, fmt == fmt']

{-| The shared wording every language's @--if@/@--of@ "default:" help text is
built from, wrapped around that language's own @ext -> format@ list. -}
extensionDeductionSentence :: String -> String
extensionDeductionSentence extList =
  "deduced from the file extension ("
    <> extList
    <> "); any other extension, or reading from stdin/writing to stdout, defaults to textual"

-- The explanation of the default embedded in the @--if@/@--of@ help text,
-- shared between the input and output variants.
extensionDeductionNote :: String -> [(String, Maybe String, Format)] -> String
extensionDeductionNote textualExt table = extensionDeductionSentence (extensionHelp textualExt table)

{-| Build the full @--if@/@--of@ help text for a format option: @kind@ (e.g.
@"Input"@ or @"Output"@), the list of allowed values, and a note on how the
default is chosen. Kept as two separate sentences, so the note (e.g. "deduced
from the file extension") doesn't read as if it's parenthetically attached to
the last format in the list (e.g. @blueprint@). -}
formatOptionHelp :: String -> String -> String -> String
formatOptionHelp kind formats note = kind ++ " format: " ++ formats ++ ". Default: " ++ note ++ "."

-- | The formats named in a format table.
supportedFormats :: [(String, Maybe String, Format)] -> [Format]
supportedFormats table = [v | (_, _, v) <- table]

{-| Generic extension-based format deduction, shared by every language's
input-format resolver: an explicit @--if@ always wins; otherwise look up the
input file's extension with @fromExt@, falling back to @deflt@ for stdin or an
extension @fromExt@ doesn't recognise. -}
deduceInputFormat :: (FilePath -> Maybe fmt) -> fmt -> Maybe fmt -> Input -> fmt
deduceInputFormat _ _ (Just fmt) _ = fmt
deduceInputFormat fromExt deflt Nothing (FileInput path) = fromMaybe deflt (fromExt path)
deduceInputFormat _ deflt Nothing StdInput = deflt

{-| The output-format counterpart of 'deduceInputFormat': an explicit @--of@
always wins; otherwise look up the output file's extension with @fromExt@,
falling back to @deflt@ for stdout, the silent sink, or an unrecognised
extension. -}
deduceOutputFormat :: (FilePath -> Maybe fmt) -> fmt -> Maybe fmt -> Output -> fmt
deduceOutputFormat _ _ (Just fmt) _ = fmt
deduceOutputFormat fromExt deflt Nothing (FileOutput path) = fromMaybe deflt (fromExt path)
deduceOutputFormat _ deflt Nothing _ = deflt

{-| Work out which input format to use, deducing from the input file's
extension (using @textualExt@ as this language's own textual extension)
restricted to @supported@ (eg @.hex@ isn't deduced for the @plc@ command,
which only handles textual and Flat). -}
resolveInputFormat :: String -> [Format] -> Maybe Format -> Input -> Format
resolveInputFormat textualExt supported =
  deduceInputFormat (supportedFormatFromExtension textualExt supported) Textual

-- | The output-format counterpart of 'resolveInputFormat'.
resolveOutputFormat :: String -> [Format] -> Maybe Format -> Output -> Format
resolveOutputFormat textualExt supported =
  deduceOutputFormat (supportedFormatFromExtension textualExt supported) Textual

-- | 'formatFromExtension', restricted to the formats in @supported@.
supportedFormatFromExtension :: String -> [Format] -> FilePath -> Maybe Format
supportedFormatFromExtension textualExt supported path =
  case formatFromExtension textualExt path of
    Just fmt | fmt `elem` supported -> Just fmt
    _ -> Nothing

{-| The @--if@/@--input-format@ option without a default, so we can tell whether
the user supplied it and deduce the format from the file extension if not. -}
inputformatOptional :: Parser (Maybe Format)
inputformatOptional =
  optional $
    option
      (maybeReader formatReader)
      ( long "if"
          <> long "input-format"
          <> metavar "FORMAT"
          <> completeWith formatNames
          <> help (formatOptionHelp "Input" formatHelp (extensionDeductionNote ".uplc" formatTable))
      )

{-| An input stream together with its format, deducing the format from the
file extension when @--if@ is not given. See 'resolveInputFormat'. -}
inputWithFormat :: Parser (Input, Format)
inputWithFormat =
  (\inp mfmt -> (inp, resolveInputFormat ".uplc" (supportedFormats formatTable) mfmt inp))
    <$> input
    <*> inputformatOptional

{-| Like 'inputWithFormat' but for commands taking a list of input files: each
file is paired with the format to read it with. When @--if@ is given it forces
that format for every file; otherwise each file's format is deduced
independently from its own extension. -}
filesWithFormats :: Parser [(FilePath, Format)]
filesWithFormats =
  ( \fs mfmt -> [(f, resolveInputFormat ".uplc" (supportedFormats formatTable) mfmt (FileInput f)) | f <- fs]
  )
    <$> files
    <*> inputformatOptional

outputformat :: Parser Format
outputformat =
  option
    (maybeReader formatReader)
    ( long "of"
        <> long "output-format"
        <> metavar "FORMAT"
        <> value Textual
        <> showDefault
        <> completeWith formatNames
        <> help ("Output format: " ++ formatHelp)
    )

{-| The @--of@/@--output-format@ option without a default, so we can tell
whether the user supplied it and deduce the format from the @-o@ file extension
if not. -}
outputformatOptional :: Parser (Maybe Format)
outputformatOptional =
  optional $
    option
      (maybeReader formatReader)
      ( long "of"
          <> long "output-format"
          <> metavar "FORMAT"
          <> completeWith formatNames
          <> help (formatOptionHelp "Output" formatHelp (extensionDeductionNote ".uplc" formatTable))
      )

{-| An output stream together with its format, deducing the format from the
file extension when @--of@ is not given. See 'resolveOutputFormat'. -}
outputWithFormat :: Parser (Output, Format)
outputWithFormat =
  (\outp mfmt -> (outp, resolveOutputFormat ".uplc" (supportedFormats formatTable) mfmt outp))
    <$> output
    <*> outputformatOptional

tracemode :: Parser TraceMode
tracemode =
  option
    auto
    ( long "trace-mode"
        <> metavar "MODE"
        <> value None
        <> showDefault
        <> completeWith (map show [(minBound :: TraceMode) .. maxBound])
        <> help "Mode for trace output."
    )

files :: Parser Files
files =
  some
    ( argument
        str
        ( metavar "[FILES...]"
            <> action "file"
            <> help "Input files; each file's format is deduced from its own extension unless --if is given"
        )
    )

applyOpts :: Parser ApplyOptions
applyOpts =
  (\fps (outp, ofmt) mode -> ApplyOptions fps outp ofmt mode)
    <$> filesWithFormats
    <*> outputWithFormat
    <*> printmode

printmode :: Parser PrintMode
printmode =
  option
    auto
    ( long "print-mode"
        <> metavar "MODE"
        <> value Classic
        <> showDefault
        <> completeWith (map show [(minBound :: PrintMode) .. maxBound])
        <> help
          ( "Print mode for textual output (ignored elsewhere): Classic -> plcPrettyClassic, "
              <> "Simple -> plcPrettyClassicSimple, "
              <> "Readable -> prettyPlcReadable, ReadableSimple -> prettyPlcReadableSimple"
          )
    )

nameformat :: Parser NameFormat
nameformat =
  flag
    IdNames
    DeBruijnNames
    ( long "debruijn"
        <> short 'j'
        <> help "Output evaluation result with de Bruijn indices (default: show textual names)"
    )

certifier :: Parser Certifier
certifier =
  optional $
    strOption
      ( long "certify"
          <> help
            ( "[EXPERIMENTAL] Produce a certificate ARG.agda proving that the program"
                <> " transformaton is correct; the certificate is an Agda proof object, which"
                <> " can be checked using the Agda proof assistant"
            )
      )

printOpts :: Parser PrintOptions
printOpts = PrintOptions <$> input <*> output <*> printmode

convertOpts :: Parser ConvertOptions
convertOpts =
  (\(inp, ifmt) (outp, ofmt) mode -> ConvertOptions inp ifmt outp ofmt mode)
    <$> inputWithFormat
    <*> outputWithFormat
    <*> printmode

certifierOutputMode :: Parser CertifierOutputMode
certifierOutputMode =
  asum
    [ flag'
        CertBasic
        ( long "certifier-basic"
            <> help "Certifier produces basic output"
        )
    , CertReport
        <$> strOption
          ( long "certifier-report"
              <> metavar "REPORT_FILE"
              <> action "file"
              <> help "Certifier writes a report to the given file"
          )
    , flag
        CertProject
        CertProject
        ( long "certifier-project"
            <> help "Certifier produces an Agda project that can be type checked (default)"
        )
    ]

cseWhichSubtermsTable :: [(String, UPLC.CseWhichSubterms)]
cseWhichSubtermsTable =
  [ ("all", UPLC.AllSubterms)
  , ("exclude-work-free", UPLC.ExcludeWorkFree)
  ]

optimizeOpts :: Parser (UPLC.OptimizeOpts name a)
optimizeOpts = do
  _ooMaxSimplifierIterations <-
    option
      auto
      ( long "opt-simplifier-iterations"
          <> metavar "INT"
          <> value (UPLC.defaultOptimizeOpts ^. UPLC.ooMaxSimplifierIterations)
          <> showDefault
          <> help "Number of simplifier iterations"
      )
  _ooMaxCseIterations <-
    option
      auto
      ( long "opt-cse-iterations"
          <> metavar "INT"
          <> value (UPLC.defaultOptimizeOpts ^. UPLC.ooMaxCseIterations)
          <> showDefault
          <> help "Number of CSE iterations"
      )
  _ooCseWhichSubterms <-
    option
      (maybeReader (`lookup` cseWhichSubtermsTable))
      ( long "opt-cse-which-subterms"
          <> metavar "MODE"
          <> value UPLC.ExcludeWorkFree
          <> showDefaultWith (showByTable cseWhichSubtermsTable)
          <> completeWith (map fst cseWhichSubtermsTable)
          <> help ("CSE subterm selection: " <> intercalate " | " (map fst cseWhichSubtermsTable))
      )
  _ooConservativeOpts <-
    switch
      ( long "opt-conservative"
          <> help "Use conservative optimisation options. May result in less optimized code."
      )
  let _ooInlineHints = UPLC.defaultOptimizeOpts ^. UPLC.ooInlineHints
  _ooInlineConstants <-
    flag
      True
      False
      ( long "opt-no-inline-constants"
          <> help "Disable constant inlining"
      )
  _ooInlineUnconditionalGrowth <-
    option
      (AstSize <$> auto)
      ( long "opt-inline-unconditional-growth"
          <> metavar "INT"
          <> value (UPLC.defaultOptimizeOpts ^. UPLC.ooInlineUnconditionalGrowth)
          <> showDefault
          <> help "Maximum allowed AST growth for unconditional inlining"
      )
  _ooInlineCallsiteGrowth <-
    option
      (AstSize <$> auto)
      ( long "opt-inline-callsite-growth"
          <> metavar "INT"
          <> value (UPLC.defaultOptimizeOpts ^. UPLC.ooInlineCallsiteGrowth)
          <> showDefault
          <> help "Maximum allowed AST growth for callsite inlining"
      )
  _ooPreserveLogging <-
    switch
      ( long "opt-preserve-logging"
          <> help
            ( "Prevent optimizations from removing or reordering log messages."
                <> " May result in less optimized code."
            )
      )
  _ooApplyToCase <-
    flag
      True
      False
      ( long "opt-no-apply-to-case"
          <> help "Disable apply-to-case optimization"
      )
  _ooHoistPolyBuiltins <-
    flag
      True
      False
      ( long "opt-no-hoist-polymorphic-builtins"
          <> help "Disable hoist-polymorphic-builtins optimization"
      )
  _ooCertifiedOptsOnly <-
    flag
      False
      True
      ( long "certified-opts-only"
          <> help
            "Run only those optimisation passes which are certified to preserve the functional behavior of the original program."
      )
  pure UPLC.OptimizeOpts {..}

evalArgKindTable :: [(String, EvalArgKind)]
evalArgKindTable =
  [ ("prog", ArgProg)
  , ("data", ArgData)
  ]

optimiseEvalOpts :: Parser OptimiseEvalOpts
optimiseEvalOpts =
  mkOpts
    <$> switch
      ( long "eval"
          <> help
            "Evaluate the program (using the CEK machine) at every stage of \
            \the optimization pipeline.  CPU and memory costs are then shown \
            \in the optimization report, alongside AST sizes, for every pass. \
            \With --certify, the same costs and sizes are also recorded in the \
            \certifier report.  Use --eval-apply or --eval-args-dir to supply \
            \arguments, if any."
      )
    <*> many
      ( strOption
          ( long "eval-apply"
              <> metavar "FILE"
              <> action "file"
              <> help
                "Apply program to this argument file before evaluating \
                \(repeatable).  Implies --eval."
          )
      )
    <*> option
      (maybeReader (`lookup` evalArgKindTable))
      ( long "eval-arg-kind"
          <> metavar (intercalate "|" (map fst evalArgKindTable))
          <> value ArgData
          <> showDefaultWith (showByTable evalArgKindTable)
          <> completeWith (map fst evalArgKindTable)
          <> help
            "Whether --eval-apply arguments are UPLC programs or Data objects"
      )
    <*> optional
      ( strOption
          ( long "eval-args-dir"
              <> metavar "DIR"
              <> action "directory"
              <> help
                "Directory with per-validator argument files for blueprint \
                \optimisation.  For each validator titled T, it looks for \
                \files DIR/T/0, DIR/T/1, ... containing arguments to apply. \
                \Implies --eval."
          )
      )
  where
    -- If the user supplied any --eval-apply or --eval-args-dir,
    -- treat --eval as implied even if they didn't pass it explicitly.
    mkOpts eval argFiles argKind argsDir =
      OptimiseEvalOpts
        { oeEval =
            eval
              || not (null argFiles)
              || isJust argsDir
        , oeArgFiles = argFiles
        , oeArgKind = argKind
        , oeBlueprintArgsDir = argsDir
        }

optimiseOpts :: Parser (OptimiseOptions name a)
optimiseOpts =
  ( \(inp, ifmt) (outp, ofmt) mode cert certOut sopts eopts ->
      OptimiseOptions inp ifmt outp ofmt mode cert certOut sopts eopts
  )
    <$> inputWithFormat
    <*> outputWithFormat
    <*> printmode
    <*> certifier
    <*> certifierOutputMode
    <*> optimizeOpts
    <*> optimiseEvalOpts

exampleMode :: Parser ExampleMode
exampleMode = exampleAvailable <|> exampleSingle

exampleAvailable :: Parser ExampleMode
exampleAvailable =
  flag'
    ExampleAvailable
    ( long "available"
        <> short 'a'
        <> help "Show available examples"
    )

exampleName :: Parser ExampleName
exampleName =
  strOption
    ( long "single"
        <> metavar "NAME"
        <> short 's'
        <> help "Show a single example"
    )

exampleSingle :: Parser ExampleMode
exampleSingle = ExampleSingle <$> exampleName

exampleOpts :: Parser ExampleOptions
exampleOpts = ExampleOptions <$> exampleMode

builtinSemanticsVariantTable :: [(String, BuiltinSemanticsVariant DefaultFun)]
builtinSemanticsVariantTable =
  [ ("A", DefaultFunSemanticsVariantA)
  , ("B", DefaultFunSemanticsVariantB)
  , ("C", DefaultFunSemanticsVariantC)
  , ("D", DefaultFunSemanticsVariantD)
  , ("E", DefaultFunSemanticsVariantE)
  ]

builtinSemanticsVariantReader :: String -> Maybe (BuiltinSemanticsVariant DefaultFun)
builtinSemanticsVariantReader = (`lookup` builtinSemanticsVariantTable)

-- This is used to make the help message show you what you actually need to type.
showBuiltinSemanticsVariant :: BuiltinSemanticsVariant DefaultFun -> String
showBuiltinSemanticsVariant = showByTable builtinSemanticsVariantTable

builtinSemanticsVariant :: Parser (BuiltinSemanticsVariant DefaultFun)
builtinSemanticsVariant =
  option
    (maybeReader builtinSemanticsVariantReader)
    ( long "builtin-semantics-variant"
        <> short 'S'
        <> metavar "VARIANT"
        <> value DefaultFunSemanticsVariantE
        <> showDefaultWith showBuiltinSemanticsVariant
        <> completeWith (map fst builtinSemanticsVariantTable)
        <> help
          ( "Builtin semantics variant: "
              <> intercalate ", " [name <> " -> " <> show v | (name, v) <- builtinSemanticsVariantTable]
          )
    )

-- Specialised parsers for PLC (TPLC), which only supports textual and Flat
-- formats. The @serialised@, @hex@ and @blueprint@ formats are not implemented
-- for TPLC (the 'ProgramLike PlcProg' instance's
-- 'loadASTfromSerialised'/'loadASTfromHex'/'serialiseAST' are unimplemented, and
-- 'runErase'/'runOptimisations' reject them), so we must not offer them.

plcFormatTable :: [(String, Maybe String, Format)]
plcFormatTable =
  [ ("textual", Nothing, Textual)
  , ("flat-named", Just "names", Flat Named)
  , ("flat", Just "de Bruijn indices", Flat DeBruijn)
  , ("flat-deBruijn", Just "alias for flat", Flat DeBruijn)
  , ("flat-namedDeBruijn", Just "names and de Bruijn indices", Flat NamedDeBruijn)
  ]

plcFormatHelp :: String
plcFormatHelp =
  intercalate
    ", "
    [maybe name (\d -> name <> " (" <> d <> ")") mdesc | (name, mdesc, _) <- plcFormatTable]

plcFormatReader :: String -> Maybe Format
plcFormatReader s = listToMaybe [v | (name, _, v) <- plcFormatTable, name == s]

plcFormatNames :: [String]
plcFormatNames = [name | (name, _, _) <- plcFormatTable]

{-| The @--if@ option for @plc@, without a default so the format can be deduced
from the file extension when it isn't given. -}
plcInputFormatOptional :: Parser (Maybe Format)
plcInputFormatOptional =
  optional $
    option
      (maybeReader plcFormatReader)
      ( long "if"
          <> long "input-format"
          <> metavar "FORMAT"
          <> completeWith plcFormatNames
          <> help (formatOptionHelp "Input" plcFormatHelp (extensionDeductionNote ".plc" plcFormatTable))
      )

{-| The @--of@ option for @plc@, without a default so the format can be deduced
from the file extension when it isn't given. -}
plcOutputFormatOptional :: Parser (Maybe Format)
plcOutputFormatOptional =
  optional $
    option
      (maybeReader plcFormatReader)
      ( long "of"
          <> long "output-format"
          <> metavar "FORMAT"
          <> completeWith plcFormatNames
          <> help (formatOptionHelp "Output" plcFormatHelp (extensionDeductionNote ".plc" plcFormatTable))
      )

plcInputWithFormat :: Parser (Input, Format)
plcInputWithFormat =
  (\inp mfmt -> (inp, resolveInputFormat ".plc" (supportedFormats plcFormatTable) mfmt inp))
    <$> input
    <*> plcInputFormatOptional

plcFilesWithFormats :: Parser [(FilePath, Format)]
plcFilesWithFormats =
  ( \fs mfmt -> [(f, resolveInputFormat ".plc" (supportedFormats plcFormatTable) mfmt (FileInput f)) | f <- fs]
  )
    <$> files
    <*> plcInputFormatOptional

plcOutputWithFormat :: Parser (Output, Format)
plcOutputWithFormat =
  (\outp mfmt -> (outp, resolveOutputFormat ".plc" (supportedFormats plcFormatTable) mfmt outp))
    <$> output
    <*> plcOutputFormatOptional

plcApplyOpts :: Parser ApplyOptions
plcApplyOpts =
  (\fps (outp, ofmt) mode -> ApplyOptions fps outp ofmt mode)
    <$> plcFilesWithFormats
    <*> plcOutputWithFormat
    <*> printmode

plcConvertOpts :: Parser ConvertOptions
plcConvertOpts =
  (\(inp, ifmt) (outp, ofmt) mode -> ConvertOptions inp ifmt outp ofmt mode)
    <$> plcInputWithFormat
    <*> plcOutputWithFormat
    <*> printmode

plcOptimiseOpts :: Parser (OptimiseOptions name a)
plcOptimiseOpts =
  ( \(inp, ifmt) (outp, ofmt) mode cert certOut sopts eopts ->
      OptimiseOptions inp ifmt outp ofmt mode cert certOut sopts eopts
  )
    <$> plcInputWithFormat
    <*> plcOutputWithFormat
    <*> printmode
    <*> certifier
    <*> certifierOutputMode
    <*> optimizeOpts
    <*> optimiseEvalOpts

-- Specialised parsers for PIR, which only supports ASTs over the Textual and
-- Named types.

pirFormatTable :: [(String, Maybe String, PirFormat)]
pirFormatTable =
  [ ("textual", Nothing, TextualPir)
  , ("flat-named", Just "names", FlatNamed)
  ]

pirFormatHelp :: String
pirFormatHelp =
  intercalate
    " or "
    [maybe name (\d -> name <> " (" <> d <> ")") mdesc | (name, mdesc, _) <- pirFormatTable]

pirFormatReader :: String -> Maybe PirFormat
pirFormatReader s = listToMaybe [v | (name, _, v) <- pirFormatTable, name == s]

pirFormatNames :: [String]
pirFormatNames = [name | (name, _, _) <- pirFormatTable]

-- File extensions recognised for PIR: its own textual extension, plus flat
-- encoding (PIR doesn't support de Bruijn names, so unlike UPLC/PLC there's
-- only one flat variant to recognise).
pirExtensionTable :: [(String, PirFormat)]
pirExtensionTable =
  [ (".pir", TextualPir)
  , (".flat", FlatNamed)
  ]

{-| Guess the PIR format from a file name's extension. Returns 'Nothing' for
an unrecognised extension, in which case callers fall back to 'TextualPir'. -}
pirFormatFromExtension :: FilePath -> Maybe PirFormat
pirFormatFromExtension path = lookup (takeExtension path) pirExtensionTable

-- The parenthetical explanation embedded in the PIR @--if@/@--of@ "default:"
-- help text, shared between the input and output variants.
pirExtensionDeductionNote :: String
pirExtensionDeductionNote =
  extensionDeductionSentence
    (intercalate ", " [ext <> " -> " <> show fmt | (ext, fmt) <- pirExtensionTable])

{-| Work out which PIR format to use. An explicit @--if@/@--of@ always wins;
otherwise the format is deduced from the file's extension, falling back to
'TextualPir' for stdin/stdout or an unrecognised extension. -}
resolvePirInputFormat :: Maybe PirFormat -> Input -> PirFormat
resolvePirInputFormat = deduceInputFormat pirFormatFromExtension TextualPir

-- | The output-format counterpart of 'resolvePirInputFormat'.
resolvePirOutputFormat :: Maybe PirFormat -> Output -> PirFormat
resolvePirOutputFormat = deduceOutputFormat pirFormatFromExtension TextualPir

{-| The @--if@ option for @pir@, without a default so the format can be deduced
from the file extension when it isn't given. -}
pPirInputFormatOptional :: Parser (Maybe PirFormat)
pPirInputFormatOptional =
  optional $
    option
      (maybeReader pirFormatReader)
      ( long "if"
          <> long "input-format"
          <> metavar "PIR-FORMAT"
          <> completeWith pirFormatNames
          <> help (formatOptionHelp "Input" pirFormatHelp pirExtensionDeductionNote)
      )

{-| The @--of@ option for @pir@, without a default so the format can be deduced
from the file extension when it isn't given. -}
pPirOutputFormatOptional :: Parser (Maybe PirFormat)
pPirOutputFormatOptional =
  optional $
    option
      (maybeReader pirFormatReader)
      ( long "of"
          <> long "output-format"
          <> metavar "PIR-FORMAT"
          <> completeWith pirFormatNames
          <> help (formatOptionHelp "Output" pirFormatHelp pirExtensionDeductionNote)
      )

{-| An input stream together with its PIR format, deducing the format from the
file extension when @--if@ is not given. See 'resolvePirInputFormat'. -}
pPirInputWithFormat :: Parser (Input, PirFormat)
pPirInputWithFormat =
  (\inp mfmt -> (inp, resolvePirInputFormat mfmt inp))
    <$> input
    <*> pPirInputFormatOptional

{-| An output stream together with its PIR format, deducing the format from
the file extension when @--of@ is not given. See 'resolvePirOutputFormat'. -}
pPirOutputWithFormat :: Parser (Output, PirFormat)
pPirOutputWithFormat =
  (\outp mfmt -> (outp, resolvePirOutputFormat mfmt outp))
    <$> output
    <*> pPirOutputFormatOptional

-- Which language: PLC or UPLC?

languageTable :: [(String, Language)]
languageTable =
  [ ("plc", PLC)
  , ("uplc", UPLC)
  ]

languageReader :: String -> Maybe Language
languageReader = (`lookup` languageTable)

pLanguage :: Parser Language
pLanguage =
  option
    (maybeReader languageReader)
    ( long "language"
        <> short 'l'
        <> metavar "LANGUAGE"
        <> value UPLC
        <> showDefaultWith (showByTable languageTable)
        <> completeWith (map fst languageTable)
        <> help ("Target language: " <> intercalate " or " (map fst languageTable))
    )
