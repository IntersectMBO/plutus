{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Control.Lens hiding (argument, set', (<.>))
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Coerce
import Data.Csv qualified as Csv
-- editorconfig-checker-disable-file
import Data.IntMap qualified as IM
import Data.List (sortOn)
import Data.Text qualified as T
import GHC.Generics
import Options.Applicative
import PlutusCore qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Error (ParserErrorBundle (..))
import PlutusCore.Executable.Common hiding (runPrint)
import PlutusCore.Executable.Parsers
import PlutusCore.Quote (runQuoteT)
import PlutusIR as PIR
import PlutusIR.Analysis.RetainedSize qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Core.Plated
import PlutusPrelude
import Text.Megaparsec (errorBundlePretty)
import UntypedPlutusCore qualified as UPLC

type PLCTerm  = PlcTerm (PIR.Provenance ())
type PIRError = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRCompilationCtx a = PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a


-- | A specialised format type for PIR. We don't support deBruijn or named deBruijn for PIR.
data PirFormat = TextualPir | FlatNamed
instance Show PirFormat
    where show = \case { TextualPir  -> "textual"; FlatNamed -> "flat-named" }

pirFormatHelp :: String
pirFormatHelp =
  "textual or flat-named (names)"

pirFormatReader :: String -> Maybe PirFormat
pirFormatReader =
    \case
         "textual"    -> Just TextualPir
         "flat-named" -> Just FlatNamed
         "flat"       -> Just FlatNamed
         _            -> Nothing

data Language = PLC | UPLC
instance Show Language
    where show = \case { PLC  -> "plc"; UPLC -> "uplc" }

languageReader :: String -> Maybe Language
languageReader =
    \case
         "plc"  -> Just PLC
         "uplc" -> Just UPLC
         _      -> Nothing


-- | Compilation options: target language, whether to optimise or not, input and output streams and types
data CompileOptions =
    CompileOptions Language
                   Bool   -- Optimise or not
                   Bool   -- True -> just report if compilation was successful; False -> write output
                   Input
                   PirFormat
                   Output
                   Format
                   PrintMode


---------------- Option parsers ----------------

-- | Invert a switch: return False if the switch is supplied on the command
-- line, True otherwise.  This is used for command-line options to turn things
-- off.
switch' :: Mod FlagFields Bool -> Parser Bool
switch' = fmap not . switch

pLanguage :: Parser Language
pLanguage = option (maybeReader languageReader)
  (  long "language"
  <> short 'l'
  <> metavar "LANGUAGE"
  <> value UPLC
  <> showDefault
  <> help ("Target language: plc or uplc")
  )

pOptimise :: Parser Bool
pOptimise = switch'
            (  long "dont-optimise"
            <> long "dont-optimize"
            <> help ("Turn off optimisations")
            )

pInputFormat :: Parser PirFormat
pInputFormat = option (maybeReader pirFormatReader)
  (  long "if"
  <> long "input-format"
  <> metavar "PIR-FORMAT"
  <> value TextualPir
  <> showDefault
  <> help ("Input format: " ++ pirFormatHelp))

pJustTest :: Parser Bool
pJustTest = switch ( long "test"
                   <> help "Just report success or failure, don't produce an output file"
                   )

pCompileOpts :: Parser CompileOptions
pCompileOpts = CompileOptions
               <$> pLanguage
               <*> pOptimise
               <*> pJustTest
               <*> input
               <*> pInputFormat
               <*> output
               <*> outputformat
               <*> printmode

data Command = Analyse  IOSpec
             | Compile  COpts
             | Compile2  CompileOptions
             | Convert  ConvertOptions
             | Optimise OptimiseOptions
             | Print    PrintOptions

data COpts = COpts
  { cIn       :: Input
  , cOptimize :: Bool
  }

pCOpts :: Parser COpts
pCOpts = COpts
            <$> input
            <*> switch' ( long "dont-optimize"
                        <> help "Don't optimize"
                        )

pPirOpts :: Parser Command
pPirOpts = hsubparser $
             command "analyse"
                  (info (Analyse <$> ioSpec) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise and analyse the program, " <>
                   "looking for variables with the largest retained size.")
           <> command "compile"
                  (info (Compile <$> pCOpts) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise it, " <>
                   "and test if it can be successfully compiled to PLC.")
           <> command "compile2"
                  (info (Compile2 <$> pCompileOpts) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise it, " <>
                   "and test if it can be successfully compiled to PLC.")
           <> command "convert"
                  (info (Convert <$> convertOpts)
                   (progDesc $
                    "Convert a program between various formats" <>
                    "(only 'textual' (default) and 'flat-named' are available for PIR)."))
           <> command "optimise"
                  (info (Optimise <$> optimiseOpts)
                   (progDesc "Run the PIR optimisation pipeline on the input."))
           <> command "print"
                  (info (Print <$> printOpts) $
                 progDesc $
                   "Given a PIR program in flat format, " <>
                   "deserialise it and print it out textually.")

-- | Load flat pir and deserialize it
loadPir :: Input -> IO (PirProg ())
loadPir = loadASTfromFlat Named


getPirProgram ::
    PirFormat ->
    Input ->
    IO (PirProg PLC.SourcePos)
getPirProgram fmt inp =
    case fmt of
        TextualPir -> parseInput inp
        FlatNamed -> do
            prog <- loadTplcASTfromFlat Named inp  :: IO (PirProg ())
            -- No source locations in Flat, so we have to make them up.
            return $ PLC.topSourcePos <$ prog


---------------- Compilation ----------------

compileToPlc :: COpts -> PirProg () -> Either PIRError PLCTerm
compileToPlc opts (PIR.Program _ pirT) = do
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
    let pirCtx = defaultCompilationCtx plcTcConfig
    runExcept $ flip runReaderT pirCtx $ runQuoteT $ PIR.compileTerm pirT
  where
    set' :: Lens' (PIR.CompilationOpts a) b
      -> (COpts -> b)
      -> PIRCompilationCtx a
      -> PIRCompilationCtx a
    set' pirOpt opt = set (PIR.ccOpts . pirOpt) (opt opts)

    defaultCompilationCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun
      -> PIRCompilationCtx a
    defaultCompilationCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig
      & set' PIR.coOptimize cOptimize

loadPirAndCompile :: COpts -> IO ()
loadPirAndCompile copts = do
    pirProg <- loadPir $ cIn copts
    putStrLn "!!! Compiling"
    case compileToPlc copts pirProg of
        Left pirError -> error $ show pirError
        Right _       -> putStrLn "!!! Compilation successful"

compileToUplc :: PLC.CompilationOpts Name () -> PlcProg () -> Either e (UplcProg ())
compileToUplc opts plcProg =
    runExcept $ flip runReaderT opts $ runQuoteT $ PLC.compileProgram plcProg


loadPirAndCompile2 :: CompileOptions -> IO ()
loadPirAndCompile2 (CompileOptions language optimise test inp ifmt outp ofmt mode)  = do
    pirProg <- getPirProgram ifmt inp :: IO (PirProg PLC.SourcePos)
    if test then putStrLn "!!! Compiling" else pure ()
    let pirCompilerOpts = COpts inp optimise
    -- Now compile to plc, maybe optimising
    case compileToPlc pirCompilerOpts (() <$ pirProg) of
      Left pirError -> error $ show pirError
      Right plcTerm ->
          let plcProg = PLC.Program () (PLC.defaultVersion ()) (() <$ plcTerm)
          in case language of
            PLC  -> if test
                    then putStrLn "!!! Compilation successful"
                    else writeProgram outp ofmt mode plcProg
            UPLC -> do  -- compile the PLC to UPLC
              let plcCompilerOpts =
                      if optimise
                      then PLC.defaultCompilationOpts
                      else PLC.defaultCompilationOpts & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
              case compileToUplc plcCompilerOpts plcProg of
                Right uplcProg ->
                    if test
                    then putStrLn "!!! Compilation successful"
                    else writeProgram outp ofmt mode uplcProg
                Left _e -> pure ()


---------------- Optimisation ----------------

doOptimisations :: PirTerm PLC.SourcePos -> Either PIRError (PirTerm ())
doOptimisations term = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let ctx = PIR.toDefaultCompilationCtx plcTcConfig
  let term' = (PIR.Original ()) <$ term
  opt <- runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.simplifyTerm term'
  pure $ (() <$ opt)

-- | Run the PIR optimisations
runOptimisations:: OptimiseOptions -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode) = do
  Program _ term <- getProgram ifmt inp :: IO (PirProg PLC.SourcePos)
  case doOptimisations term of
    Left e  -> error $ show e
    Right t -> writeProgram outp ofmt mode (Program () t)


---------------- Analysis ----------------

-- | a csv-outputtable record row of {name,unique,size}
data RetentionRecord = RetentionRecord { name :: T.Text, unique :: Int, size :: PIR.Size}
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.Size

loadPirAndAnalyse :: IOSpec -> IO ()
loadPirAndAnalyse ioSpecs = do
    -- load pir and make sure that it is globally unique (required for retained size)
    PIR.Program _ pirT <- PLC.runQuote . PLC.rename <$> loadPir (inputSpec ioSpecs)
    putStrLn "!!! Analysing for retention"
    let
        -- all the variable names (tynames coerced to names)
        names = pirT ^.. termSubtermsDeep.termBindings.bindingNames ++
                pirT ^.. termSubtermsDeep.termBindings.bindingTyNames.coerced
        -- a helper lookup table of uniques to their textual representation
        nameTable :: IM.IntMap T.Text
        nameTable = IM.fromList [(coerce $ _nameUnique n , _nameText n) | n <- names]

        -- build the retentionMap
        retentionMap = PIR.termRetentionMap def pirT
        -- sort the map by decreasing retained size
        sortedRetained = sortOn (negate . snd) $ IM.assocs retentionMap

        -- change uniques to texts and use csv-outputtable records
        sortedRecords :: [RetentionRecord]
        sortedRecords =
          sortedRetained <&> \(i, s) ->
            RetentionRecord (IM.findWithDefault "given key is not in map" i nameTable) i s

    -- encode to csv and output it
    Csv.encodeDefaultOrderedByName sortedRecords &
        case outputSpec ioSpecs of
            FileOutput path -> BSL.writeFile path
            StdOutput       -> BSL.putStr


---------------- Parse and print a PIR source file ----------------
-- This option for PIR source file does NOT check for @UniqueError@'s.
-- Only the print option for PLC or UPLC files check for them.

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions iospec _mode) = do
    let inputPath = inputSpec iospec
    contents <- getInput inputPath
    -- parse the program
    case parseNamedProgram (show inputPath) contents of
      -- when fail, pretty print the parse errors.
      Left (ParseErrorB err) ->
          errorWithoutStackTrace $ errorBundlePretty err
      -- otherwise,
      Right (p::PirProg PLC.SourcePos) -> do
        -- pretty print the program. Print mode may be added later on.
        let
            printed :: String
            printed = show $ pretty p
        case outputSpec iospec of
            FileOutput path -> writeFile path printed
            StdOutput       -> putStrLn printed


---------------- Main ----------------

main :: IO ()
main = do
    comm <- customExecParser (prefs showHelpOnEmpty) infoOpts
    case comm of
        Analyse  opts -> loadPirAndAnalyse opts
        Compile  opts -> loadPirAndCompile opts
        Compile2 opts -> loadPirAndCompile2 opts
        Convert  opts -> runConvert @PirProg opts
        Optimise opts -> runOptimisations opts
        Print    opts -> runPrint opts
  where
    infoOpts =
      info (pPirOpts <**> helper)
           ( fullDesc
           <> header "PIR tool"
           <> progDesc ("This program provides a number of utilities for dealing with "
           <> "PIR programs, including print, analysis, and compilation to PLC."))

