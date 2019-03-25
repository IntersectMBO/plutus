-- | @boolean@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Bool
    ( bool
    , true
    , false
    , ifThenElse
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.Unit

-- | 'Bool' as a PLC type.
--
-- > all (A :: *). A -> A -> A
bool :: Type TyName ()
bool = runQuote $ do
    a <- freshTyName () "a"
    return
        . TyForall () a (Type ())
        $ mkIterTyFun () [ TyVar () a, TyVar () a ]
        $ TyVar () a

-- | 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> x
true :: TermLike term TyName Name => term ()
true = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . tyAbs () a (Type ())
       $ mkIterLamAbs [
          VarDecl () x (TyVar () a),
          VarDecl () y (TyVar () a)
          ]
       $ var () x

-- | 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : A) -> y
false :: TermLike term TyName Name => term ()
false = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    y <- freshName () "y"
    return
       . tyAbs () a (Type ())
       $ mkIterLamAbs [
          VarDecl () x (TyVar () a),
          VarDecl () y (TyVar () a)
          ]
       $ var () y

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> b {() -> A} x y ()
ifThenElse :: TermLike term TyName Name => term ()
ifThenElse = runQuote $ do
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () unit (TyVar () a)
    return
       . tyAbs () a (Type ())
      $ mkIterLamAbs [
          VarDecl () b bool,
          VarDecl () x unitFunA,
          VarDecl () y unitFunA
          ]
      $ mkIterApp ()
          (tyInst () (var () b) unitFunA)
          [var () x, var () y, unitval]
