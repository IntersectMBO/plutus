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
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Type

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). A -> A -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        $ mkIterTyFun [ TyVar () a, TyVar () a ]
        $ TyVar () a

-- | 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> x
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . TyAbs () a (Type ())
       $ mkIterLamAbs [
          (x, TyVar () a),
          (y, TyVar () a)
          ]
       $ Var () x

-- | 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> y
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . TyAbs () a (Type ())
       $ mkIterLamAbs [
          (x, TyVar () a),
          (y, TyVar () a)
          ]
       $ Var () y

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b {() -> A} x y ()
getBuiltinIf :: Quote (Value TyName Name ())
getBuiltinIf = do
    unit1 <- getBuiltinUnit
    unit2 <- getBuiltinUnit
    unit3 <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    builtinBool <- getBuiltinBool
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA u = TyFun () u (TyVar () a)
    return
       . TyAbs () a (Type ())
      $ mkIterLamAbs [
          (b, builtinBool),
          (x, unitFunA unit1),
          (y, unitFunA unit2)
          ]
      $ mkIterApp
          (TyInst () (Var () b) (TyFun () unit3 (TyVar () a)))
          [Var () x, Var () y, unitval]
