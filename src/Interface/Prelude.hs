{-# OPTIONS -Wall #-}







-- | This module defines the standard library of Plutus.

module Interface.Prelude where

import Elaboration.Contexts
import qualified PlutusCore.Program as Core
import Interface.Integration

import System.FilePath
import Paths_plutus_prototype




prelude :: IO Core.Program
prelude = do
{- proof-development-experiment
  preludePath <- getDataFileName "src/Prelude.pls"
  src <- readFile preludePath
  case loadProgram emptyDeclContext src of
    Left err -> error ("Error while loading Plutus prelude: " ++ err)
    Right x -> return x
-}
  mbRes <- runElabInContexts [] . loadProgram <$> preludeString
  case mbRes of
    Left err -> error ("Error while parsing Plutus prelude: " ++ err)
    Right x  -> return x

-- | Prelude as a string, useful for compiling it into the binary
preludeString :: IO String
preludeString = readFile =<< getDataFileName ("src" </> "Prelude.pls")
