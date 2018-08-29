-- | Combinators.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Function
    ( getBuiltinConst
    , getBuiltinSelf
    , getBuiltinUnroll
    , getBuiltinFix
    ) where

import           Language.PlutusCore.Quote
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.StdLib.Type

-- | 'const' as a PLC term.
--
-- > /\ (A B :: *) -> \(x : A) (y : B) -> x
getBuiltinConst :: Quote (Term TyName Name ())
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

-- | @Self@ as a PLC type.
--
-- > \(a :: *) -> fix \(self :: *) -> self -> a
getBuiltinSelf :: Quote (HoledType TyName ())
getBuiltinSelf = do
    a    <- freshTyName () "a"
    self <- freshTyName () "self"
    return
        . HoledType self $ \hole ->
          TyLam () a (Type ())
        . hole
        . TyFun () (TyVar () self)
        $ TyVar () a

-- | @unroll@ as a PLC term.
--
-- > /\(a :: *) -> \(s : self a) -> unwrap s s
getBuiltinUnroll :: Quote (Term TyName Name ())
getBuiltinUnroll = do
    builtinSelf <- getBuiltinSelf
    a <- freshTyName () "a"
    s <- freshName () "s"
    let RecursiveType _ builtinSelfA =
            holedToRecursive . holedTyApp builtinSelf $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () s builtinSelfA
        . Apply () (Unwrap () $ Var () s)
        $ Var () s

-- | 'fix' as a PLC term.
--
-- > /\(a b :: *) -> \(f : (a -> b) -> a -> b) ->
-- >    unroll {a -> b} (wrap \(s : self (a -> b)) \(x : a) -> f (unroll {a -> b} s) x)
getBuiltinFix :: Quote (Term TyName Name ())
getBuiltinFix = do
    self   <- getBuiltinSelf
    unroll <- getBuiltinUnroll
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    f <- freshName () "f"
    s <- freshName () "s"
    x <- freshName () "x"
    let funAB = TyFun () (TyVar () a) $ TyVar () b
        unrollFunAB = TyInst () unroll funAB
        RecursiveType wrapSelfFunAB selfFunAB =
            holedToRecursive $ holedTyApp self funAB
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () f (TyFun () funAB funAB)
        . Apply () unrollFunAB
        . wrapSelfFunAB
        . LamAbs () s selfFunAB
        . LamAbs () x (TyVar () a)
        . foldl (Apply ()) (Var () f)
        $ [ Apply () unrollFunAB $ Var () s
          , Var () x
          ]
