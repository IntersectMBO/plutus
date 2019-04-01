-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( succInteger
    ) where

import           Language.PlutusCore.Constant.Make (makeDynBuiltinIntSizedAs)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > /\(s :: size) -> \(i : integer s) ->
-- >     addInteger {s} i (resizeInteger {1} {s} (sizeOfInteger {s} i) 1!1)
succInteger :: TermLike term TyName Name => term ()
succInteger = runQuote $ do
    s <- freshTyName () "s"
    i  <- freshName () "i"
    return
        . tyAbs () s (Size ())
        . lamAbs () i (TyApp () (TyBuiltin () TyInteger) $ TyVar () s)
        . mkIterApp () (tyInst () (builtin () $ BuiltinName () AddInteger) $ TyVar () s)
        $ [ var () i
          , makeDynBuiltinIntSizedAs (TyVar () s) (var () i) 1
          ]
