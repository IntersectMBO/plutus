-- | Scott-encoded @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.ScottUnit
    ( unit
    , unitval
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | '()' as a PLC type.
--
-- > all (A :: *). A -> A
unit :: Type TyName uni ()
unit = runQuote $ do
    a <- freshTyName "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
unitval :: TermLike term TyName Name uni fun => term ()
unitval = runQuote $ do
    a <- freshTyName "a"
    x <- freshName "x"
    return
        . tyAbs  () a (Type ())
        . lamAbs () x (TyVar () a)
        $ var () x
