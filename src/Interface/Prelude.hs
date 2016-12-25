{-# OPTIONS -Wall #-}







-- | This module defines the standard library of Plutus.

module Interface.Prelude where

import qualified PlutusCore.Program as Core
import Interface.Integration

import Paths_plutus_prototype




prelude :: IO Core.Program
prelude = do
  preludePath <- getDataFileName "src/Prelude.pls"
  mbRes <- runElabInContexts [] . loadProgram <$> readFile preludePath
  case mbRes of
    Left err -> error ("Error while parsing Plutus prelude: " ++ err)
    Right x  -> return x
