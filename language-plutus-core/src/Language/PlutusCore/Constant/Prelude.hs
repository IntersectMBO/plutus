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

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

type Size = Natural
type Value = Term

-- | Church-encoded 'const' as a PLC type.
--
-- > /\ (A B :: *) -> \(x : A) (y : B) -> x
getBuiltinConst :: Fresh (Term TyName Name ())
getBuiltinConst = do
    a <- freshTyName () "A"
    b <- freshTyName () "B"
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () y (TyVar () b)
        $ Var () x

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Fresh (Type TyName ())
getBuiltinUnit = do
    a <- freshTyName () "A"
    return
        . TyForall () a (Type ())
        . TyFun () (TyVar () a)
        $ TyVar () a

-- | Church-encoded '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Fresh (Value TyName Name ())
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
getBuiltinBool :: Fresh (Type TyName ())
getBuiltinBool = do
    unit <- getBuiltinUnit
    a <- freshTyName () "A"
    return
        . TyForall () a (Type ())
        . TyFun () (TyFun () unit (TyVar () a))
        . TyFun () (TyFun () unit (TyVar () a))
        $ TyVar () a

-- | Church-encoded 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Fresh (Value TyName Name ())
getBuiltinTrue = do
    builtinUnit    <- getBuiltinUnit
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
getBuiltinFalse :: Fresh (Value TyName Name ())
getBuiltinFalse = do
    builtinUnit    <- getBuiltinUnit
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

-- | Church-encoded @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b x y
getBuiltinIf :: Fresh (Value TyName Name ())
getBuiltinIf = do
    builtinUnit <- getBuiltinUnit
    builtinBool <- getBuiltinBool
    a <- freshTyName () "A"
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
