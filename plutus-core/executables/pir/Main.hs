{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Common
import Control.Lens hiding (argument, set', (<.>))
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Data.ByteString qualified as BS
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Coerce
import Data.Csv qualified as Csv
import Data.IntMap qualified as IM
import Data.List (sortOn)
import Data.Text qualified as T
import Flat (unflat)
import GHC.Generics
import Options.Applicative
import Parsers
import PlutusCore qualified as PLC
import PlutusCore.Quote (runQuoteT)
import PlutusIR as PIR
import PlutusIR.Analysis.RetainedSize qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core.Plated
import Prettyprinter

data Command = Analyse AOpts
             | Compile COpts
             | Print POpts

data AOpts = AOpts
  {
    aIn  :: Input
  , aOut :: Output
  }

data COpts = COpts
  { cIn       :: Input
  , cOptimize :: Bool
  }

data POpts = POpts
  {
    pIn  :: Input
  , pOut :: Output
  }

pAOpts :: Parser AOpts
pAOpts = AOpts
    <$> input
    <*> output

pCOpts :: Parser COpts
pCOpts = COpts
            <$> input
            <*> switch' ( long "dont-optimize"
                        <> help "Don't optimize"
                        )
  where
    switch' :: Mod FlagFields Bool -> Parser Bool
    switch' = fmap not . switch

pPOpts :: Parser POpts
pPOpts = POpts
    <$> input
    <*> output

pPirOpts :: Parser Command
pPirOpts = hsubparser $
    command "analyse"
        (info (Analyse <$> pAOpts) $
            progDesc "Given a PIR program in flat format, deserialise and analyse the program looking for variables with the largest retained size.")
  <> command "compile"
        (info (Compile <$> pCOpts) $
            progDesc "Given a PIR program in flat format, deserialise it and test if it can be successfully compiled to PLC.")
  <> command "print"
        (info (Print <$> pPOpts) $
            progDesc "Given a PIR program in flat format, deserialise it and print it out textually.")


type PIRTerm  = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
type PLCTerm  = PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRError = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRCompilationCtx a = PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a

compile :: COpts -> PIRTerm -> Either PIRError PLCTerm
compile opts pirT = do
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
    let pirCtx = defaultCompilationCtx plcTcConfig
    runExcept $ flip runReaderT pirCtx $ runQuoteT $ PIR.compileTerm pirT
  where
    set' :: Lens' (PIR.CompilationOpts a) b -> (COpts -> b) -> PIRCompilationCtx a -> PIRCompilationCtx a
    set' pirOpt opt = set (PIR.ccOpts . pirOpt) (opt opts)

    defaultCompilationCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun -> PIRCompilationCtx a
    defaultCompilationCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig
      & set' PIR.coOptimize                     cOptimize

loadPirAndCompile :: COpts -> IO ()
loadPirAndCompile copts = do
    pirT <- loadPir $ cIn copts
    putStrLn "!!! Compiling"
    case compile copts pirT of
        Left pirError -> error $ show pirError
        Right _       -> putStrLn "!!! Compilation successful"

loadPirAndAnalyse :: AOpts -> IO ()
loadPirAndAnalyse aopts = do
    -- load pir and make sure that it is globally unique (required for retained size)
    pirT <- PLC.runQuote . PLC.rename <$> loadPir (aIn aopts)
    putStrLn "!!! Analysing for retention"
    let
        -- all the variable names (tynames coerced to names)
        names = pirT ^.. termSubtermsDeep.termBindings.bindingNames ++
                pirT ^.. termSubtermsDeep.termBindings.bindingTyNames.coerced
        -- a helper lookup table of uniques to their textual representation
        nameTable :: IM.IntMap T.Text
        nameTable = IM.fromList [(coerce $ nameUnique n , nameString n) | n <- names]

        -- build the retentionMap
        retentionMap = PIR.termRetentionMap pirT
        -- sort the map by decreasing retained size
        sortedRetained = sortOn (negate . snd) $ IM.assocs retentionMap

        -- change uniques to texts and use csv-outputtable records
        sortedRecords :: [RetentionRecord]
        sortedRecords = (\(i,s) -> RetentionRecord (IM.findWithDefault "???" i nameTable) i s) <$> sortedRetained

    -- encode to csv and output it
    Csv.encodeDefaultOrderedByName sortedRecords &
        case aOut aopts of
            FileOutput path -> BSL.writeFile path
            StdOutput       -> BSL.putStr

loadPirAndPrint :: POpts -> IO ()
loadPirAndPrint popts = do
    pirT <- loadPir $ pIn popts
    let
        printed :: String
        printed = show $ pretty pirT
    case pOut popts of
        FileOutput path -> writeFile path printed
        StdOutput       -> putStrLn printed

-- | Load flat pir and deserialize it
loadPir :: Input -> IO PIRTerm
loadPir inp =do
    bs <- case inp of
             FileInput path -> do
                 putStrLn $ "!!! Loading file " ++ path
                 BS.readFile path
             StdInput -> BS.getContents
    case unflat bs of
        Left decodeErr -> error $ show decodeErr
        Right pirT     -> pure pirT

main :: IO ()
main = do
    comm <- customExecParser (prefs showHelpOnEmpty) infoOpts
    case comm of
        Analyse opts -> loadPirAndAnalyse opts
        Compile opts -> loadPirAndCompile opts
        Print opts   -> loadPirAndPrint opts
  where
    infoOpts =
      info (pPirOpts <**> helper)
           ( fullDesc
           <> progDesc "Load a flat pir term from file and run the compiler on it"
           <> header "pir - a small tool for loading pir from flat representation for analysis or compilation to PLC")

-- | a csv-outputtable record row of {name,unique,size}
data RetentionRecord = RetentionRecord { name :: T.Text, unique :: Int, size :: PIR.Size}
    deriving stock (Generic, Show)
    deriving anyclass Csv.ToNamedRecord
    deriving anyclass Csv.DefaultOrdered
deriving newtype instance Csv.ToField PIR.Size
