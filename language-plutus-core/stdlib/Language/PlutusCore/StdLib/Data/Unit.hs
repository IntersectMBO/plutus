-- | @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Unit
    ( unit
    , unitval
    , sequ
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- | '()' as a PLC type.
--
-- > all (A :: *). A -> A
unit :: Type TyName ()
unit = runQuote $ do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
unitval :: TermLike term TyName Name => term ()
unitval = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyVar () a)
        $ var () x

-- | 'seq' specified to '()' as a PLC term.
--
-- > \(x y : unit) -> unitval
sequ :: TermLike term TyName Name => term ()
sequ = runQuote $ do
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . lamAbs () x unit
        . lamAbs () y unit
        $ unitval
