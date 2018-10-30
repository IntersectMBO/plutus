-- | @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Unit
    ( getBuiltinUnit
    , getBuiltinUnitval
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

-- | '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Quote (Type TyName ())
getBuiltinUnit = rename =<< do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Quote (Value TyName Name ())
getBuiltinUnitval = rename =<< do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        $ Var () x
