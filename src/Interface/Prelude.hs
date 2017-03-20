{-# OPTIONS -Wall #-}







-- | This module defines the standard library of Plutus.

module Interface.Prelude where

import Elaboration.Contexts
import qualified PlutusCore.Program as Core
import Interface.Integration

import Paths_plutus_prototype




prelude :: IO Core.Program
prelude = do
  preludePath <- getDataFileName "src/Prelude.pls"
  src <- readFile preludePath
  case loadProgram emptyDeclContext src of
    Left err -> error ("Error while loading Plutus prelude: " ++ err)
    Right x -> return x