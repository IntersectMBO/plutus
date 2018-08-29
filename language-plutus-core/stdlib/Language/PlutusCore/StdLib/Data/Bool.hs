-- | @boolean@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Bool
    ( getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ) where

import           Language.PlutusCore.Quote
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.StdLib.Data.Unit

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). (() -> A) -> (() -> A) -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = do
    unit <- getBuiltinUnit
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyFun () unit (TyVar () a))
        . TyFun () (TyFun () unit (TyVar () a))
        $ TyVar () a

-- | 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = do
    builtinUnit    <- getBuiltinUnit
    builtinUnitval <- getBuiltinUnitval
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () builtinUnit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ Apply () (Var () x) builtinUnitval

-- | 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = do
    builtinUnit    <- getBuiltinUnit
    builtinUnitval <- getBuiltinUnitval
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () builtinUnit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ Apply () (Var () y) builtinUnitval

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b x y
getBuiltinIf :: Quote (Value TyName Name ())
getBuiltinIf = do
    builtinUnit <- getBuiltinUnit
    builtinBool <- getBuiltinBool
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () builtinUnit (TyVar () a)
    return
       . TyAbs () a (Type ())
       . LamAbs () b builtinBool
       . LamAbs () x unitFunA
       . LamAbs () y unitFunA
       $ foldl (Apply ())
           (TyInst () (Var () b) (TyVar () a))
           [Var () x, Var () y]
