{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Main (main) where

import Control.Lens
import Control.Monad.Except
import MyScript
import PlutusCore.Pretty (prettyClassic, render)
import PlutusCore.Quote (runQuoteT)
import PlutusTx.Code (getPlcNoAnn)
import System.Environment (getArgs)
import UntypedPlutusCore as UPLC

unDeBruijn
  :: UPLC.Program NamedDeBruijn DefaultUni DefaultFun ()
  -> UPLC.Program Name DefaultUni DefaultFun ()
unDeBruijn p =
  case runExcept @UPLC.FreeVariableError $
    runQuoteT $
      traverseOf UPLC.progTerm UPLC.unDeBruijnTerm p of
    Left e   -> error (show e)
    Right p' -> p'

main :: IO ()
main = do
  [path] <- getArgs
  writeFile path . render . prettyClassic . unDeBruijn $ getPlcNoAnn compiledLen
