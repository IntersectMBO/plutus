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
import PlutusIR.Analysis.VarInfo
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Core.Plated
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC

import Control.Lens (coerced, (^..))
import Control.Monad (when)
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


{- Note [De Bruijn indices and PIR]
   The `plc` and `uplc` commands both support ASTs whose "names" are de Bruijn
   indices.  These aren't supported for PIR because PIR has `Let` blocks of
   possibly mutually recursive definitions and it's not clear whether de Bruijn
   indices (or levels) really make sense in the presence of mutual recursion
   since scopes aren't properly nested in that case: if we process the AST in
   the normal way then a declaration may have to refer to another variable which
   hasn't yet been declared.  It may be possible to overcome this by allowing
   scopes which introduce multiple variables at once, but this would require
   some lookahead or CPS-type technique which would lead to quite complex code
   for a feature that we don't really need.
-}

---------------- Types for command line options ----------------

data PirOptimiseOptions = PirOptimiseOptions Input PirFormat Output PirFormat PrintMode

data PirConvertOptions = PirConvertOptions Input PirFormat Output PirFormat PrintMode

-- | So that we can just use the generic `runConvert` function but still
-- disallow unsupported name types.
toConvertOptions :: PirConvertOptions -> ConvertOptions
toConvertOptions (PirConvertOptions inp ifmt outp ofmt mode) =
    ConvertOptions inp (pirFormatToFormat ifmt) outp (pirFormatToFormat ofmt) mode

data AnalyseOptions = AnalyseOptions Input PirFormat Output -- Input is a program, output is text

-- | Compilation options: target language, whether to optimise or not, input and output streams and types
data CompileOptions =
    CompileOptions Language
                   Bool   -- Optimise or not?
                   Bool   -- True -> just report if compilation was successful; False -> write output
                   Input
                   PirFormat
                   Output
                   Format
                   PrintMode

data Command = Analyse  AnalyseOptions
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

-- | Whether to perform optimisations or not.  The default here is True,
-- ie *do* optimise; specifying --dont-optimise returns False.
pOptimise :: Parser Bool
pOptimise = flag True False
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
               <*> pPirInputFormat
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
                  (info (Convert <$> pPirConvertOptions)
                   (progDesc $ "Convert a program between textual and flat-named format."))
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

compileToPlc :: Bool -> PirProg () -> Either (PirError UnitProvenance) (PlcProg ())
compileToPlc optimise p = do
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
    let ctx = getCtx plcTcConfig
    plcProg <- runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.compileProgram p
    pure $ () <$ plcProg
  where
    getCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun
      -> PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a
    getCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig
         & PIR.ccOpts . PIR.coOptimize .~ optimise
    -- See PlutusIR.Compiler.Types.CompilerOpts for other compilation flags,
    -- including coPedantic, which causes the result of every stage in the
    -- pipeline to be typechecked.

compileToUplc :: Bool -> PlcProg () -> UplcProg ()
compileToUplc optimise plcProg =
    let plcCompilerOpts =
            if optimise
            then PLC.defaultCompilationOpts
            else PLC.defaultCompilationOpts & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
    in flip runReader plcCompilerOpts $ runQuoteT $ PLC.compileProgram plcProg

loadPirAndCompile :: CompileOptions -> IO ()
loadPirAndCompile (CompileOptions language optimise test inp ifmt outp ofmt mode)  = do
    pirProg <- readProgram (pirFormatToFormat ifmt) inp
    when test $ putStrLn "!!! Compiling"
    -- Now compile to plc, maybe optimising
    case compileToPlc optimise (() <$ pirProg) of
      Left pirError -> error $ show pirError
      Right plcProg ->
          case language of
            PLC  -> if test
                    then putStrLn "!!! Compilation successful"
                    else writeProgram outp ofmt mode plcProg
            UPLC -> do  -- compile the PLC to UPLC
              let uplcProg = compileToUplc optimise plcProg
              if test then putStrLn "!!! Compilation successful"
              else writeProgram outp ofmt mode uplcProg


---------------- Optimisation ----------------

doOptimisations :: PirTerm PLC.SrcSpan -> Either (PirError UnitProvenance) (PirTerm UnitProvenance)
doOptimisations term = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let ctx = getCtx plcTcConfig
  runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.simplifyTerm =<< PLC.rename (PIR.Original () <$ term)
  where
    getCtx
        :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun
        -> PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a
    getCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig
         & PIR.ccOpts . PIR.coOptimize .~ True
         -- This is on by default anyway, but let's make certain.

-- | Run the PIR optimisations
runOptimisations:: PirOptimiseOptions -> IO ()
runOptimisations (PirOptimiseOptions inp ifmt outp ofmt mode) = do
  Program _ _ term <- readProgram (pirFormatToFormat ifmt) inp
  case doOptimisations term of
    Left e  -> error $ show e
    Right t -> writeProgram outp (pirFormatToFormat ofmt) mode
               (Program () PLC.latestVersion(() <$ t))


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
    p :: PirProg PLC.SrcSpan <- readProgram (pirFormatToFormat ifmt) inp
    let PIR.Program _ _ term = PLC.runQuote . PLC.rename $ () <$ p
    putStrLn "!!! Analysing for retention"
    let
        -- all the variable names (tynames coerced to names)
        names = term ^.. termSubtermsDeep.termBindings.bindingNames ++
                term ^.. termSubtermsDeep.termBindings.bindingTyNames.coerced
        -- a helper lookup table of uniques to their textual representation
        nameTable :: IM.IntMap T.Text
        nameTable = IM.fromList [(coerce $ _nameUnique n , _nameText n) | n <- names]

        -- build the retentionMap
        retentionMap = PIR.termRetentionMap def (termVarInfo term) term
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
            -- NoOutput supresses the output of programs/terms, but that's not
            -- what we've got here.
            NoOutput        -> BSL.putStr

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
            NoOutput        -> pure ()

---------------- Main ----------------

main :: IO ()
main = do
    comm <- customExecParser (prefs showHelpOnEmpty) infoOpts
    case comm of
        Analyse  opts -> loadPirAndAnalyse opts
        Compile  opts -> loadPirAndCompile opts
        Convert  opts -> runConvert @PirProg (toConvertOptions opts)
        Optimise opts -> runOptimisations opts
        Print    opts -> runPrint opts
  where
    infoOpts =
      info (pPirOptions <**> helper)
           ( fullDesc
           <> header "PIR tool"
           <> progDesc ("This program provides a number of utilities for dealing with "
           <> "PIR programs, including printing, analysis, optimisation, and compilation to UPLC and PLC."))

