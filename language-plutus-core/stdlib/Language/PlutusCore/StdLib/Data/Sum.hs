-- | @sum@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Sum
    ( getBuiltinSum
    , getBuiltinLeft
    , getBuiltinRight
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           Language.PlutusCore.Type

-- | 'Either' as a PLC type.
--
-- > \(a b :: *) -> all (r :: *). (a -> r) -> (b -> r) -> r
getBuiltinSum :: Quote (Type TyName ())
getBuiltinSum = rename =<< do
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    r <- freshTyName () "r"
    return
        . TyLam () a (Type ())
        . TyLam () b (Type ())
        . TyForall () r (Type ())
        . TyFun () (TyFun () (TyVar () a) . TyFun () (TyVar () b) $ TyVar () r)
        $ TyVar () r

-- | 'Left' as a PLC term.
--
-- > /\(a b :: *) -> \(x : a) -> /\(r :: *) -> \(f : a -> r) -> (g : b -> r) -> f x
getBuiltinLeft :: Quote (Term TyName Name ())
getBuiltinLeft = rename =<< do
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    x <- freshName () "x"
    r <- freshTyName () "r"
    f <- freshName () "f"
    g <- freshName () "g"
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () x (TyVar () a)
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () a) $ TyVar () r)
        . LamAbs () g (TyFun () (TyVar () b) $ TyVar () r)
        . Apply () (Var () f)
        $ Var () x

-- | 'Right' as a PLC term.
--
-- > /\(a b :: *) -> \(y : b) -> /\(r :: *) -> \(f : a -> r) -> (g : b -> r) -> g y
getBuiltinRight :: Quote (Term TyName Name ())
getBuiltinRight = rename =<< do
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    y <- freshName () "y"
    r <- freshTyName () "r"
    f <- freshName () "f"
    g <- freshName () "g"
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () y (TyVar () b)
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () a) $ TyVar () r)
        . LamAbs () g (TyFun () (TyVar () b) $ TyVar () r)
        . Apply () (Var () g)
        $ Var () y
