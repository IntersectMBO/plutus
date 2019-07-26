{-# LANGUAGE OverloadedStrings #-}
-- | Meta-functions relating to functions.
module Language.PlutusCore.StdLib.Meta.Data.Function where

import           PlutusPrelude

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- | 'const' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> t
constPartial :: TermLike term TyName Name => term () -> term ()
constPartial t = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyVar () a)
        $ t
