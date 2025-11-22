-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- NOTE:
-- This module defines CSV instances for PIR types.
-- Orphan warnings are disabled intentionally because the PIR library
-- does not expose appropriate instance modules for these types.

module Main where

import Data.Version.Extras (gitAwareVersionInfo)
import Paths_plutus_executables qualified as Paths
import PlutusCore qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Error (ParserErrorBundle (..))
import PlutusCore.Executable.Common hiding (runPrint)
import PlutusCore.Executable.Parsers
import PlutusCore.Quote (runQuote, runQuoteT)
import PlutusIR as PIR
import PlutusIR.Analysis.RetainedSize qualified as PIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Core.Plated
import PlutusPrelude
import Text.Megaparsec (errorBundlePretty)
import UntypedPlutusCore qualified as UPLC

import Control.Lens (coerced, (^..))
import Control.Monad (when)
import Control.Monad.Except (modifyError, runExcept)
import Control.Monad.Reader (runReaderT)
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Csv qualified as Csv
import Data.IntMap qualified as IM
import Data.List (sortOn)
import Data.Ord (Down(..))
import Data.Text qualified as T
import Options.Applicative
import System.Exit (exitFailure)

type PirError a = PIR.Error PLC.DefaultUni PLC.DefaultFun a
type UnitProvenance = PIR.Provenance ()

---------------- Types for command line options ----------------

data PirOptimiseOptions = PirOptimiseOptions Input PirFormat Output PirFormat PrintMode
data PirConvertOptions  = PirConvertOptions Input PirFormat Output PirFormat PrintMode
data AnalyseOptions     = AnalyseOptions Input PirFormat Output

data CompileOptions =
    CompileOptions Language
                   Bool
                   Bool
                   Input
                   PirFormat
                   Output
                   Format
                   PrintMode

data Command
    = Analyse  AnalyseOptions
    | Compile  CompileOptions
    | Convert  PirConvertOptions
    | Optimise PirOptimiseOptions
    | Print    PrintOptions

---------------- Option parsers ----------------

pPirOptimiseOptions :: Parser PirOptimiseOptions
pPirOptimiseOptions = PirOptimiseOptions <$> input <*> pPirInputFormat <*> output <*> pPirOutputFormat <*> printmode

pPirConvertOptions :: Parser PirConvertOptions
pPirConvertOptions = PirConvertOptions <$> input <*> pPirInputFormat <*> output <*> pPirOutputFormat <*> printmode

pAnalyseOptions :: Parser AnalyseOptions
pAnalyseOptions = AnalyseOptions <$> input <*> pPirInputFormat <*> output

pOptimise :: Parser Bool
pOptimise = flag True False
    (  long "dont-optimise"
    <> long "dont-optimize"
    <> help "Turn off optimisations"
    )

pJustTest :: Parser Bool
pJustTest = switch
    ( long "test"
   <> help "Just report success or failure, don't produce an output file"
    )

pCompileOptions :: Parser CompileOptions
pCompileOptions =
    CompileOptions
        <$> pLanguage
        <*> pOptimise
        <*> pJustTest
        <*> input
        <*> pPirInputFormat
        <*> output
        <*> outputformat
        <*> printmode

pPirOptions :: Parser Command
pPirOptions = hsubparser $
      command "analyse"
        (analyse "Given a PIR program in flat format, deserialise and analyse retained size.")
   <> command "analyze"
        (analyse "Same as 'analyse'.")
   <> command "compile"
        (info (Compile <$> pCompileOptions)
              (progDesc "Deserialise PIR and test compilation to PLC."))
   <> command "convert"
        (info (Convert <$> pPirConvertOptions)
              (progDesc "Convert between textual and flat PIR formats."))
   <> command "optimise"
        (optimise "Run PIR optimisation pipeline.")
   <> command "optimize"
        (optimise "Same as 'optimise'.")
   <> command "print"
        (info (Print <$> printOpts)
              (progDesc "Read PIR source and print it in the selected format."))

  where
    analyse desc  = info (Analyse <$> pAnalyseOptions) (progDesc desc)
    optimise desc = info (Optimise <$> pPirOptimiseOptions) (progDesc desc)

---------------- Compilation ----------------

compileToPlc
    :: Bool
    -> PirProg ()
    -> Either (PirError UnitProvenance) (PlcProg ())
compileToPlc optimise p = do
    plcTcConfig <- modifyError (PIR.PLCError . PLC.TypeErrorE)
                               (PLC.getDefTypeCheckConfig PIR.noProvenance)
    let ctx = PIR.toDefaultCompilationCtx plcTcConfig
                & PIR.ccOpts . PIR.coOptimize .~ optimise

    plcProg <- runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.compileProgram p
    pure (void plcProg)

compileToUplc :: Bool -> PlcProg () -> UplcProg ()
compileToUplc optimise plcProg =
    let opts =
            if optimise
            then PLC.defaultCompilationOpts
            else PLC.defaultCompilationOpts
                    & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
    in runQuote $ flip runReaderT opts $ PLC.compileProgram plcProg

loadPirAndCompile :: CompileOptions -> IO ()
loadPirAndCompile (CompileOptions language optimise test inp ifmt outp ofmt mode) = do
    pirProg <- readProgram (pirFormatToFormat ifmt) inp
    when test $ putStrLn "[PIR] Compiling..."

    case compileToPlc optimise (void pirProg) of
        Left pirErr -> do
            putStrLn "[ERROR] PIR → PLC compilation failed:"
            print pirErr
            exitFailure

        Right plcProg ->
            case language of
                PLC ->
                    if test
                    then putStrLn "[OK] Compilation successful"
                    else writeProgram outp ofmt mode plcProg

                UPLC -> do
                    let uplc = compileToUplc optimise plcProg
                    if test
                    then putStrLn "[OK] Compilation successful"
                    else writeProgram outp ofmt mode uplc

---------------- Optimisation ----------------

doOptimisations
    :: PirTerm PLC.SrcSpan
    -> Either (PirError UnitProvenance) (PirTerm UnitProvenance)
doOptimisations term = do
    plcTcConfig <- modifyError (PIR.PLCError . PLC.TypeErrorE)
                               (PLC.getDefTypeCheckConfig PIR.noProvenance)
    let ctx = PIR.toDefaultCompilationCtx plcTcConfig
                & PIR.ccOpts . PIR.coOptimize .~ True

    runExcept $ flip runReaderT ctx $ runQuoteT $
        PIR.runCompilerPass PIR.simplifier (PIR.Original () <$ term)

runOptimisations :: PirOptimiseOptions -> IO ()
runOptimisations (PirOptimiseOptions inp ifmt outp ofmt mode) = do
    prog <- readProgram (pirFormatToFormat ifmt) inp
    let Program _ _ term = prog

    case doOptimisations term of
        Left err -> do
            putStrLn "[ERROR] PIR optimisation failed:"
            print err
            exitFailure

        Right t ->
            writeProgram outp (pirFormatToFormat ofmt) mode
                (Program () PLC.latestVersion (void t))

---------------- Analysis ----------------

data RetentionRecord =
    RetentionRecord
        { name   :: T.Text
        , unique :: Int
        , size   :: PIR.AstSize
        }
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.AstSize

loadPirAndAnalyse :: AnalyseOptions -> IO ()
loadPirAndAnalyse (AnalyseOptions inp ifmt outp) = do
    p <- (readProgram (pirFormatToFormat ifmt) inp :: IO (PirProg PLC.SrcSpan))
    let PIR.Program _ _ term = runQuote . PLC.rename $ void p

    putStrLn "[PIR] Analysing retained size..."

    let names =
            term ^.. termSubtermsDeep . termBindings . bindingNames
         ++ term ^.. termSubtermsDeep . termBindings . bindingTyNames . coerced

        nameTable =
            IM.fromList
                [ (coerce (_nameUnique n), _nameText n)
                | n <- names
                ]

        retentionMap   = PIR.termRetentionMap def (termVarInfo term) term
        sortedRetained = sortOn (Down . snd) (IM.assocs retentionMap)

        records =
            [ RetentionRecord
                (IM.findWithDefault "unknown" u nameTable)
                u
                s
            | (u, s) <- sortedRetained
            ]

    let csvOut = Csv.encodeDefaultOrderedByName records

    case outp of
        FileOutput path -> BSL.writeFile path csvOut
        StdOutput       -> BSL.putStr csvOut
        NoOutput        -> BSL.putStr csvOut

---------------- Parsing and printing ----------------

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions inp outp mode) = do
    contents <- getInput inp

    case parseNamedProgram (show inp) contents of
        Left (ParseErrorB err) ->
            errorWithoutStackTrace (errorBundlePretty err)

        Right (p :: PirProg PLC.SrcSpan) -> do
            let printed = show (prettyPrintByMode mode p)
            case outp of
                FileOutput path -> writeFile path printed
                StdOutput       -> putStrLn printed
                NoOutput        -> pure ()

versioner :: Parser (a -> a)
versioner = simpleVersioner (gitAwareVersionInfo Paths.version)

---------------- Main ----------------

main :: IO ()
main = do
    cmd <- customExecParser (prefs showHelpOnEmpty) opts
    case cmd of
        Analyse  o -> loadPirAndAnalyse o
        Compile  o -> loadPirAndCompile o
        Convert  o -> runConvert @PirProg (toConvertOptions o)
        Optimise o -> runOptimisations o
        Print    o -> runPrint o
  where
    opts =
        info (pPirOptions <**> versioner <**> helper)
            ( fullDesc
           <> header "PIR tool"
           <> progDesc
                "Utilities for working with PIR programs: printing, \
                \analysis, optimisation, and compilation."
            )


