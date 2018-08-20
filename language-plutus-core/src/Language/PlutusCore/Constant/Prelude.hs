{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Constant.Prelude
    ( Size
    , Value
    , getBuiltinConst
    , getBuiltinUnit
    , getBuiltinUnitval
    , getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

type Size = Natural
type Value = Term

-- | 'const' as a PLC term.
--
-- > /\ (A B :: *) -> \(x : A) (y : B) -> x
getBuiltinConst :: Fresh (Term TyName Name ())
getBuiltinConst = do
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () y (TyVar () b)
        $ Var () x

-- | '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Fresh (Type TyName ())
getBuiltinUnit = do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Fresh (Value TyName Name ())
getBuiltinUnitval = do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        $ Var () x

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). (() -> A) -> (() -> A) -> A
getBuiltinBool :: Fresh (Type TyName ())
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
getBuiltinTrue :: Fresh (Value TyName Name ())
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
getBuiltinFalse :: Fresh (Value TyName Name ())
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
getBuiltinIf :: Fresh (Value TyName Name ())
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
