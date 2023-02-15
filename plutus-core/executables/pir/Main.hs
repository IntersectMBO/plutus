{-# LANGUAGE DeriveAnyClass    #-}
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

type PLCTerm  = PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRTerm0 = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
type PIRTerm1 = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun PLC.SourcePos
type PIRTerm  = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRTerm' = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (PIR.Provenance PLC.SourcePos)
type PIRError = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRError' = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance PLC.SourcePos)
type PIRCompilationCtx a = PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a
data Command = Analyse  IOSpec
             | Compile  COpts
             | Convert ConvertOptions
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
  where
    switch' :: Mod FlagFields Bool -> Parser Bool
    switch' = fmap not . switch

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
           <> command "convert"
                  (info (Convert <$> convertOpts)
                   (progDesc "Convert a program between various formats"))
           <> command "optimise"
                  (info (Optimise <$> optimiseOpts)
                   (progDesc "Run the PIR optimisation pipeline on the input"))
           <> command "print"
                  (info (Print <$> printOpts) $
                 progDesc $
                   "Given a PIR program in flat format, " <>
                   "deserialise it and print it out textually.")

-- | Load flat pir and deserialize it
loadPir :: Input -> IO (PirProg ())
loadPir = loadASTfromFlat Named

compile :: COpts -> PirProg () -> Either PIRError PLCTerm
compile opts (PIR.Program _ pirT) = do
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

---------------- Optimisations ----------------

doOptimisations :: PirProg PLC.SourcePos -> Either PIRError (PirProg ())
doOptimisations (Program ann body) = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let ctx = PIR.toDefaultCompilationCtx plcTcConfig
  let body' = (PIR.Original ()) <$ body
  opt <- runExcept $ flip runReaderT ctx $ runQuoteT $ PIR.simplifyTerm body'
  Right (Program () (() <$ opt))
{- case opt of
    Left e    -> Left e
    Right opt -> Right $ Program () (() <$ opt)
-}

-- | Run the PIR optimisations
runOptimisations:: OptimiseOptions -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode) = do
  prog <- getProgram ifmt inp :: IO (PirProg PLC.SourcePos)
  case doOptimisations prog of
    Left _    -> error "FAILED"
    Right opt -> writeProgram outp ofmt mode opt

loadPirAndCompile :: COpts -> IO ()
loadPirAndCompile copts = do
    pirProg <- loadPir $ cIn copts
    putStrLn "!!! Compiling"
    case compile copts pirProg of
        Left pirError -> error $ show pirError
        Right _       -> putStrLn "!!! Compilation successful"

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
      Right (p::PirProg PLC.SrcSpan) -> do
        -- pretty print the program. Print mode may be added later on.
        let
            printed :: String
            printed = show $ pretty p
        case outputSpec iospec of
            FileOutput path -> writeFile path printed
            StdOutput       -> putStrLn printed

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
      info (pPirOpts <**> helper)
           ( fullDesc
           <> header "PIR tool"
           <> progDesc ("This program provides a number of utilities for dealing with "
           <> "PIR programs, including print, analysis, and compilation to PLC."))

-- | a csv-outputtable record row of {name,unique,size}
data RetentionRecord = RetentionRecord { name :: T.Text, unique :: Int, size :: PIR.Size}
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.Size
