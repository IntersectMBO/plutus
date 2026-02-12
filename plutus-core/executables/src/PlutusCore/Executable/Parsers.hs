{-# LANGUAGE LambdaCase #-}

-- | Common option parsers for executables
module PlutusCore.Executable.Parsers where

import PlutusCore.Default (BuiltinSemanticsVariant (..), DefaultFun)
import PlutusCore.Executable.Types

import Options.Applicative

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

formatHelp :: String
formatHelp =
  "textual, flat-named (names), flat (de Bruijn indices), "
    <> "or flat-namedDeBruijn (names and de Bruijn indices)"

formatReader :: String -> Maybe Format
formatReader =
  \case
    "textual" -> Just Textual
    "flat-named" -> Just (Flat Named)
    "flat" -> Just (Flat DeBruijn)
    "flat-deBruijn" -> Just (Flat DeBruijn)
    "flat-namedDeBruijn" -> Just (Flat NamedDeBruijn)
    _ -> Nothing

inputformat :: Parser Format
inputformat =
  option
    (maybeReader formatReader)
    ( long "if"
        <> long "input-format"
        <> metavar "FORMAT"
        <> value Textual
        <> showDefault
        <> help ("Input format: " ++ formatHelp)
    )

outputformat :: Parser Format
outputformat =
  option
    (maybeReader formatReader)
    ( long "of"
        <> long "output-format"
        <> metavar "FORMAT"
        <> value Textual
        <> showDefault
        <> help ("Output format: " ++ formatHelp)
    )

tracemode :: Parser TraceMode
tracemode =
  option
    auto
    ( long "trace-mode"
        <> metavar "MODE"
        <> value None
        <> showDefault
        <> help "Mode for trace output."
    )

files :: Parser Files
files = some (argument str (metavar "[FILES...]"))

applyOpts :: Parser ApplyOptions
applyOpts = ApplyOptions <$> files <*> inputformat <*> output <*> outputformat <*> printmode

printmode :: Parser PrintMode
printmode =
  option
    auto
    ( long "print-mode"
        <> metavar "MODE"
        <> value Classic
        <> showDefault
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
convertOpts = ConvertOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

optimiseOpts :: Parser OptimiseOptions
optimiseOpts =
  OptimiseOptions
    <$> input
    <*> inputformat
    <*> output
    <*> outputformat
    <*> printmode
    <*> certifier

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

builtinSemanticsVariantReader :: String -> Maybe (BuiltinSemanticsVariant DefaultFun)
builtinSemanticsVariantReader =
  \case
    "A" -> Just DefaultFunSemanticsVariantA
    "B" -> Just DefaultFunSemanticsVariantB
    "C" -> Just DefaultFunSemanticsVariantC
    "D" -> Just DefaultFunSemanticsVariantD
    "E" -> Just DefaultFunSemanticsVariantE
    _ -> Nothing

-- This is used to make the help message show you what you actually need to type.
showBuiltinSemanticsVariant :: BuiltinSemanticsVariant DefaultFun -> String
showBuiltinSemanticsVariant =
  \case
    DefaultFunSemanticsVariantA -> "A"
    DefaultFunSemanticsVariantB -> "B"
    DefaultFunSemanticsVariantC -> "C"
    DefaultFunSemanticsVariantD -> "D"
    DefaultFunSemanticsVariantE -> "E"

builtinSemanticsVariant :: Parser (BuiltinSemanticsVariant DefaultFun)
builtinSemanticsVariant =
  option
    (maybeReader builtinSemanticsVariantReader)
    ( long "builtin-semantics-variant"
        <> short 'S'
        <> metavar "VARIANT"
        <> value DefaultFunSemanticsVariantE
        <> showDefaultWith showBuiltinSemanticsVariant
        <> help
          ( "Builtin semantics variant: A -> DefaultFunSemanticsVariantA, "
              <> "B -> DefaultFunSemanticsVariantB, "
              <> "C -> DefaultFunSemanticsVariantC, "
              <> "D -> DefaultFunSemanticsVariantD, "
              <> "E -> DefaultFunSemanticsVariantE"
          )
    )

-- Specialised parsers for PIR, which only supports ASTs over the Textual and
-- Named types.

pirFormatHelp :: String
pirFormatHelp =
  "textual or flat-named (names)"

pirFormatReader :: String -> Maybe PirFormat
pirFormatReader =
  \case
    "textual" -> Just TextualPir
    "flat-named" -> Just FlatNamed
    _ -> Nothing

pPirInputFormat :: Parser PirFormat
pPirInputFormat =
  option
    (maybeReader pirFormatReader)
    ( long "if"
        <> long "input-format"
        <> metavar "PIR-FORMAT"
        <> value TextualPir
        <> showDefault
        <> help ("Input format: " ++ pirFormatHelp)
    )

pPirOutputFormat :: Parser PirFormat
pPirOutputFormat =
  option
    (maybeReader pirFormatReader)
    ( long "of"
        <> long "output-format"
        <> metavar "PIR-FORMAT"
        <> value TextualPir
        <> showDefault
        <> help ("Output format: " ++ pirFormatHelp)
    )

-- Which language: PLC or UPLC?

languageReader :: String -> Maybe Language
languageReader =
  \case
    "plc" -> Just PLC
    "uplc" -> Just UPLC
    _ -> Nothing

pLanguage :: Parser Language
pLanguage =
  option
    (maybeReader languageReader)
    ( long "language"
        <> short 'l'
        <> metavar "LANGUAGE"
        <> value UPLC
        <> showDefaultWith (\case PLC -> "plc"; UPLC -> "uplc")
        <> help ("Target language: plc or uplc")
    )
