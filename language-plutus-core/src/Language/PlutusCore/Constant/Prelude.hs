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

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

type Size = Natural
type Value = Term

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
getBuiltinTrue :: Fresh (Value TyName Name ())
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
       $ Apply () (Var () x) (pure builtinUnitval)

-- | Church-encoded 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Fresh (Value TyName Name ())
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
       $ Apply () (Var () y) (pure builtinUnitval)
