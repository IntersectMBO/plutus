-- | @boolean@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Bool
    ( getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.Unit

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). A -> A -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = rename =<< do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        $ mkIterTyFun () [ TyVar () a, TyVar () a ]
        $ TyVar () a

-- | 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> x
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = rename =<< do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . TyAbs () a (Type ())
       $ mkIterLamAbs () [
          VarDecl () x (TyVar () a),
          VarDecl () y (TyVar () a)
          ]
       $ Var () x

-- | 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> y
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = rename =<< do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . TyAbs () a (Type ())
       $ mkIterLamAbs () [
          VarDecl () x (TyVar () a),
          VarDecl () y (TyVar () a)
          ]
       $ Var () y

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b {() -> A} x y ()
getBuiltinIf :: Quote (Value TyName Name ())
getBuiltinIf = rename =<< do
    unit <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    builtinBool <- getBuiltinBool
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () unit (TyVar () a)
    return
       . TyAbs () a (Type ())
      $ mkIterLamAbs () [
          VarDecl () b builtinBool,
          VarDecl () x unitFunA,
          VarDecl () y unitFunA
          ]
      $ mkIterApp ()
          (TyInst () (Var () b) unitFunA)
          [Var () x, Var () y, unitval]
