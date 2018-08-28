{-# OPTIONS -Wall #-}







-- | This module defines the standard library of Plutus.

module Interface.Prelude where

import           Elaboration.Contexts
import           Interface.Integration
import qualified PlutusCore.Program     as Core

import           Paths_plutus_prototype
import           System.FilePath




prelude :: IO Core.Program
prelude = do
  src <- preludeString
  case loadProgram emptyDeclContext src of
    Left err -> error ("Error while loading Plutus prelude: " ++ err)
    Right x  -> return x

-- | Prelude as a string, useful for compiling it into the binary
preludeString :: IO String
preludeString = readFile =<< getDataFileName ("src" </> "Prelude.pls")
