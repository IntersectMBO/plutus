{-# LANGUAGE RankNTypes #-}
module Main where

import qualified PlutusCore                 as PLC
import           PlutusCore.Quote           (runQuoteT)
import qualified PlutusIR                   as PIR
import qualified PlutusIR.Compiler          as PIR

import           Control.Lens               (Lens', set, (&))
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Reader
import qualified Data.ByteString            as BS
import           Flat                       (unflat)
import           Options.Applicative


data Options = Options
  { opPath     :: FilePath
  , opOptimize :: Bool
  }

options :: Parser Options
options = Options
            <$> argument str (metavar "FILE.flat")
            <*> switch' (long "dont-optimize"
                        <> help "Don't optimize"
                        )
  where
    switch' :: Mod FlagFields Bool -> Parser Bool
    switch' = fmap not . switch

type PIRTerm  = PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
type PLCTerm  = PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRError = PIR.Error PLC.DefaultUni PLC.DefaultFun (PIR.Provenance ())
type PIRCompilationCtx a = PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun a

compile
  :: Options -> PIRTerm -> Either PIRError PLCTerm
compile opts pirT = do
  plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
  let pirCtx = defaultCompilationCtx plcTcConfig
  runExcept $ flip runReaderT pirCtx $ runQuoteT $ PIR.compileTerm pirT

  where
    set' :: Lens' PIR.CompilationOpts b -> (Options -> b) -> PIRCompilationCtx a -> PIRCompilationCtx a
    set' pirOpt opt = set (PIR.ccOpts . pirOpt) (opt opts)

    defaultCompilationCtx :: PLC.TypeCheckConfig PLC.DefaultUni PLC.DefaultFun -> PIRCompilationCtx a
    defaultCompilationCtx plcTcConfig =
      PIR.toDefaultCompilationCtx plcTcConfig
      & set' PIR.coOptimize                     opOptimize

loadPirAndCompile :: Options -> IO ()
loadPirAndCompile opts = do
  let path = opPath opts
  putStrLn $ "!!! Loading file " ++ path
  bs <- BS.readFile path
  case unflat bs of
    Left decodeErr -> error $ show decodeErr
    Right pirT -> do
      putStrLn "!!! Compiling"
      case compile opts pirT of
        Left pirError -> error $ show pirError
        Right _       -> putStrLn "!!! Compilation successful"

main :: IO ()
main = loadPirAndCompile =<< execParser opts
  where
    opts =
      info (options <**> helper)
           ( fullDesc
           <> progDesc "Load a flat pir term from file and run the compiler on it"
           <> header "pir - a small tool for loading pir from flat representation and compiling it")
