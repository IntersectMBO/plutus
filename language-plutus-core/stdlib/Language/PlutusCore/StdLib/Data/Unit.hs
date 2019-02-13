-- | @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Unit
    ( unit
    , unitval
    , sequ
    ) where

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
unitval :: Value TyName Name ()
unitval = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        $ Var () x

-- | @seq @() @()@ as a PLC term.
--
-- > \(x y : unit) -> unitval
sequ :: Value TyName Name ()
sequ = runQuote $ do
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . LamAbs () x unit
        . LamAbs () y unit
        $ unitval
