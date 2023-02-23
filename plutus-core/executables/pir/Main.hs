-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

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
import UntypedPlutusCore qualified as UPLC

import Control.Lens (coerced, (^..))
import Control.Monad.Trans.Except (runExcept)
import Control.Monad.Trans.Reader (runReader, runReaderT)
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Csv qualified as Csv
import Data.IntMap qualified as IM
import Data.List (sortOn)
import Data.Text qualified as T
import Options.Applicative
import Text.Megaparsec (errorBundlePretty)

type PirError a = PIR.Error PLC.DefaultUni PLC.DefaultFun a
type UnitProvenance = PIR.Provenance ()

---------------- Types for command line options ----------------

data PirOptimiseOptions = PirOptimiseOptions Input Format Output Format PrintMode

data AnalyseOptions = AnalyseOptions Input Format Output -- Input is a program, output is text

data Language = PLC | UPLC

-- | Compilation options: target language, whether to optimise or not, input and output streams and types
data CompileOptions =
    CompileOptions Language
                   Bool   -- Optimise or not?
                   Bool   -- True -> just report if compilation was successful; False -> write output
                   Input
                   Format
                   Output
                   Format
                   PrintMode

data Command = Analyse  AnalyseOptions
             | Compile  CompileOptions
             | Convert  ConvertOptions
             | Optimise PirOptimiseOptions
             | Print    PrintOptions


---------------- Option parsers ----------------

-- | Invert a switch: return False if the switch is supplied on the command
-- line, True otherwise.  This is used for command-line options to turn things
-- off.
invertedSwitch :: Mod FlagFields Bool -> Parser Bool
invertedSwitch = fmap not . switch

pPirOptimiseOptions :: Parser PirOptimiseOptions
pPirOptimiseOptions = PirOptimiseOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

pAnalyseOptions :: Parser AnalyseOptions
pAnalyseOptions = AnalyseOptions <$> input <*> inputformat <*> output

languageReader :: String -> Maybe Language
languageReader =
    \case
         "plc"  -> Just PLC
         "uplc" -> Just UPLC
         _      -> Nothing

pLanguage :: Parser Language
pLanguage = option (maybeReader languageReader)
  (  long "language"
  <> short 'l'
  <> metavar "LANGUAGE"
  <> value UPLC
  <> showDefaultWith ( \case PLC -> "plc" ; UPLC -> "uplc" )
  <> help ("Target language: plc or uplc")
  )

pOptimise :: Parser Bool
pOptimise = invertedSwitch
            (  long "dont-optimise"
            <> long "dont-optimize"
            <> help ("Turn off optimisations")
            )

pJustTest :: Parser Bool
pJustTest = switch ( long "test"
                   <> help "Just report success or failure, don't produce an output file"
                   )

pCompileOptions :: Parser CompileOptions
pCompileOptions = CompileOptions
               <$> pLanguage
               <*> pOptimise
               <*> pJustTest
               <*> input
               <*> inputformat
               <*> output
               <*> outputformat
               <*> printmode

pPirOptions :: Parser Command
pPirOptions = hsubparser $
              command "analyse" (
                      analyse ("Given a PIR program in flat format, deserialise and analyse the program, " <>
                               "looking for variables with the largest retained size."))
           <> command "analyze" (analyse "Same as 'analyse'.")
           <> command "compile"
                  (info (Compile <$> pCompileOptions) $
                   progDesc $
                   "Given a PIR program in flat format, deserialise it, " <>
                   "and test if it can be successfully compiled to PLC.")
           <> command "convert"
                  (info (Convert <$> convertOpts)
                   (progDesc $ "Convert a program between various formats."))
           <> command "optimise" (optimise "Run the PIR optimisation pipeline on the input.")
           <> command "optimize" (optimise "Same as 'optimise'.")
           <> command "print"
                  (info (Print <$> printOpts) $
                 progDesc $
                   "Given a PIR program in textual format, " <>
                   "read it in and print it in the selected format.")
           where
             analyse desc = info (Analyse <$> pAnalyseOptions) $ progDesc desc
             optimise desc = info (Optimise <$> pPirOptimiseOptions) $ progDesc desc

---------------- Compilation ----------------

compileToPlc :: Bool -> PirProg () -> Either (PirError UnitProvenance) (PlcTerm UnitProvenance)
compileToPlc optimise (PIR.Program _ pirT) = do
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
    let pirCtx = defaultCompilationCtx plcTcConfig
    runExcept $ flip runReaderT pirCtx $ runQuoteT $ PIR.compileTerm pirT
  where
    defaultCompilationCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun
      -> PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a
    defaultCompilationCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig &
         PIR.ccOpts . PIR.coOptimize .~ optimise

compileToUplc :: Bool -> PlcProg () -> UplcProg ()
compileToUplc optimise plcProg =
    let plcCompilerOpts =
            if optimise
            then PLC.defaultCompilationOpts
            else PLC.defaultCompilationOpts & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
    in flip runReader plcCompilerOpts $ runQuoteT $ PLC.compileProgram plcProg

loadPirAndCompile :: CompileOptions -> IO ()
loadPirAndCompile (CompileOptions language optimise test inp ifmt outp ofmt mode)  = do
    pirProg <- getProgram ifmt inp :: IO (PirProg PLC.SrcSpan)
    if test then putStrLn "!!! Compiling" else pure ()
    -- Now compile to plc, maybe optimising
    case compileToPlc optimise (() <$ pirProg) of
      Left pirError -> error $ show pirError
      Right plcTerm ->
          let plcProg = PLC.Program () PLC.defaultVersion (() <$ plcTerm)
          in case language of
            PLC  -> if test
                    then putStrLn "!!! Compilation successful"
                    else writeProgram outp ofmt mode plcProg
            UPLC -> do  -- compile the PLC to UPLC
              let uplcProg = compileToUplc optimise plcProg
              if test
              then putStrLn "!!! Compilation successful"
              else writeProgram outp ofmt mode uplcProg


---------------- Optimisation ----------------

doOptimisations :: PirTerm PLC.SrcSpan -> Either (PirError UnitProvenance) (PirTerm UnitProvenance)
doOptimisations term = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let ctx = PIR.toDefaultCompilationCtx plcTcConfig
      term' = (PIR.Original ()) <$ term
  runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.simplifyTerm term'

-- | Run the PIR optimisations
runOptimisations:: PirOptimiseOptions -> IO ()
runOptimisations (PirOptimiseOptions inp ifmt outp ofmt mode) = do
  Program _ term <- getProgram ifmt inp :: IO (PirProg PLC.SrcSpan)
  case doOptimisations term of
    Left e  -> error $ show e
    Right t -> writeProgram outp ofmt mode (Program () (() <$ t))


---------------- Analysis ----------------

-- | a csv-outputtable record row of {name,unique,size}
data RetentionRecord = RetentionRecord { name :: T.Text, unique :: Int, size :: PIR.Size}
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.Size

loadPirAndAnalyse :: AnalyseOptions -> IO ()
loadPirAndAnalyse (AnalyseOptions inp ifmt outp) = do
    -- load pir and make sure that it is globally unique (required for retained size)
    p :: PirProg PLC.SrcSpan <- getProgram ifmt inp
    let PIR.Program _ pirT = PLC.runQuote . PLC.rename $ () <$ p
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
        case outp of
            FileOutput path -> BSL.writeFile path
            StdOutput       -> BSL.putStr

---------------- Parse and print a PIR source file ----------------
-- This option for PIR source file does NOT check for @UniqueError@'s.
-- Only the print options for PLC or UPLC files check for them.

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions inp outp mode) = do
    contents <- getInput inp
    -- parse the program
    case parseNamedProgram (show inp) contents of
      -- when fail, pretty print the parse errors.
      Left (ParseErrorB err) ->
          errorWithoutStackTrace $ errorBundlePretty err
      -- otherwise,
      Right (p::PirProg PLC.SrcSpan) -> do
        let
            printed :: String
            printed = show $ getPrintMethod mode p
        case outp of
            FileOutput path -> writeFile path printed
            StdOutput       -> putStrLn printed


---------------- Main ----------------

main :: IO ()
main = do
    comm <- customExecParser (prefs showHelpOnEmpty) infoOpts
    case comm of
        Analyse  opts -> loadPirAndAnalyse opts
        Compile  opts -> loadPirAndCompile opts
        Convert  opts -> runConvert @PirProg opts
        Optimise opts -> runOptimisations opts
        Print    opts -> runPrint opts
  where
    infoOpts =
      info (pPirOptions <**> helper)
           ( fullDesc
           <> header "PIR tool"
           <> progDesc ("This program provides a number of utilities for dealing with "
           <> "PIR programs, including printing, analysis, optimisation, and compilation to UPLC and PLC."))

