{-# LANGUAGE OverloadedStrings #-}
-- | Meta-functions relating to functions.
module Language.PlutusCore.StdLib.Meta.Data.Function
    ( constPartial
    , etaExpand
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | 'const' as a PLC term.
--
-- > constPartial t = /\(A :: *) -> \(x : A) -> t
constPartial :: TermLike term TyName Name uni fun => term () -> term ()
constPartial t = runQuote $ do
    a <- freshTyName "a"
    x <- freshName "x"
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyVar () a)
        $ t

-- | Eta-expand a function at a given type. Note that this has to be a \"meta\" function
-- for it not force the function it receives and instead directly hide it under a lambda.
--
-- > etaExpand ty fun = \(x : ty) -> fun x
etaExpand :: TermLike term TyName Name uni fun => Type TyName uni () -> term () -> term ()
etaExpand ty fun = runQuote $ do
    x <- freshName "x"
    return
        . lamAbs () x ty
        . apply () fun
        $ var () x
