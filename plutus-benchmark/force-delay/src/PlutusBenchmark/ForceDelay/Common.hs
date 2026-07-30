-- | This is similar to @PlutusBenchmark.Validation.Common@.
module PlutusBenchmark.ForceDelay.Common
  ( benchWith
  , unsafeUnflat
  , mkEvalCtx
  , benchTermCek
  , getScriptDirectory
  ) where

import PlutusBenchmark.Common (benchTermCek, getConfig, getDataDir, mkEvalCtx)
import PlutusBenchmark.NaturalSort
import PlutusCore.Flat
import UntypedPlutusCore qualified as UPLC

import Criterion.Main
import Criterion.Main.Options (Mode, parseWith)
import Criterion.Types (Config (..))
import Data.ByteString qualified as BS
import Options.Applicative
import System.Directory (listDirectory)
import System.FilePath

getScriptDirectory :: IO FilePath
getScriptDirectory = do
  root <- getDataDir
  return $ root </> "force-delay" </> "data"

unsafeUnflat
  :: String -> BS.ByteString -> UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
unsafeUnflat file contents =
  case unflat contents of
    Left e -> errorWithoutStackTrace $ "Flat deserialisation failure for " ++ file ++ ": " ++ show e
    Right (UPLC.UnrestrictedProgram prog) -> prog

----------------------- Main -----------------------

parserInfo :: Config -> ParserInfo Mode
parserInfo cfg =
  info (helper <*> parseWith cfg) $ header "Plutus Core force-delay benchmark suite"

benchWith :: (FilePath -> BS.ByteString -> Benchmarkable) -> IO ()
benchWith act = do
  cfg <- getConfig 20.0 -- Run each benchmark for at least 20 seconds.  Change this with -L or --timeout (longer is better).
  options <- execParser $ parserInfo cfg
  scriptDirectory <- getScriptDirectory
  files0 <- listDirectory scriptDirectory -- Just the filenames, not the full paths
  let
    -- naturalSort puts the filenames in a better order than Data.List.Sort
    files = naturalSort $ filter (isExtensionOf ".flat") files0
  runMode options $ mkBMs scriptDirectory files
  where
    -- Make benchmarks for the given files in the directory
    mkBMs :: FilePath -> [FilePath] -> [Benchmark]
    mkBMs = map . mkScriptBM

    mkScriptBM :: FilePath -> FilePath -> Benchmark
    mkScriptBM dir file =
      env (BS.readFile $ dir </> file) $ \(~scriptBS) ->
        bench (dropExtension file) $ act file scriptBS
