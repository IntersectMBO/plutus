-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( succInteger
    ) where

import           Language.PlutusCore.Constant.Make (makeIntConstant)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > \(i : integer) -> addInteger i 1
succInteger :: TermLike term TyName Name => term ()
succInteger = runQuote $ do
    i  <- freshName () "i"
    return
        . lamAbs () i (TyBuiltin () TyInteger)
        . mkIterApp () (builtin () $ BuiltinName () AddInteger)
        $ [ var () i
          , makeIntConstant 1
          ]
