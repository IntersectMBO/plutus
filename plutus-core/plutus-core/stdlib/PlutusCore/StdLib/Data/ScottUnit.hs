-- | Scott-encoded @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.StdLib.Data.ScottUnit
    ( unit
    , unitval
    ) where

import           PlutusCore.Core
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote

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
