{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Constant.Prelude
    ( Size
    , Value
    , getBuiltinUnit
    , getBuiltinUnitval
    , getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude
import           Language.PlutusCore.Quote

type Size = Natural
type Value = Term

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Quote (Type TyName ())
getBuiltinUnit = do
    a <- freshTyName () "A"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | Church-encoded '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Quote (Value TyName Name ())
getBuiltinUnitval = do
    a <- freshTyName () "A"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        $ Var () x

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). (() -> A) -> (() -> A) -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = do
    a <- freshTyName () "A"
    unit <- getBuiltinUnit
    return
        . TyForall () a (Type ())
        . TyFun () (TyFun () unit (TyVar () a))
        . TyFun () (TyFun () unit (TyVar () a))
        $ TyVar () a

-- | Church-encoded 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = do
    builtinUnit <- getBuiltinUnit
    builtinUnitval <- getBuiltinUnitval
    a <- freshTyName () "A"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () builtinUnit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ Apply () (Var () x) builtinUnitval

-- | Church-encoded 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = do
    builtinUnit <- getBuiltinUnit
    builtinUnitval <- getBuiltinUnitval
    a <- freshTyName () "A"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () builtinUnit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ Apply () (Var () y) builtinUnitval
