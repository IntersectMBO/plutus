-- | @boolean@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Bool
    ( getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). (() -> A) -> (() -> A) -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = do
    unit1 <- getBuiltinUnit
    unit2 <- getBuiltinUnit
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyFun () unit1 (TyVar () a))
        . TyFun () (TyFun () unit2 (TyVar () a))
        $ TyVar () a

-- | 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = do
    unit1   <- getBuiltinUnit
    unit2   <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA u = TyFun () u (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x (unitFunA unit1)
       . LamAbs () y (unitFunA unit2)
       $ Apply () (Var () x) unitval

-- | 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = do
    unit    <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () unit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ Apply () (Var () y) unitval

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b x y
getBuiltinIf :: Quote (Value TyName Name ())
getBuiltinIf = do
    unit1 <- getBuiltinUnit
    unit2 <- getBuiltinUnit
    builtinBool <- getBuiltinBool
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA u = TyFun () u (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () b builtinBool
       . LamAbs () x (unitFunA unit1)
       . LamAbs () y (unitFunA unit2)
       $ foldl' (Apply ())
           (TyInst () (Var () b) (TyVar () a))
           [Var () x, Var () y]
