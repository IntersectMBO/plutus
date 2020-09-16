-- | @sum@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Sum
    ( sum
    , left
    , right
    ) where

import           Prelude                   hiding (sum)

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | 'Either' as a PLC type.
--
-- > \(a b :: *) -> all (r :: *). (a -> r) -> (b -> r) -> r
sum :: Type TyName uni ()
sum = runQuote $ do
    a <- freshTyName "a"
    b <- freshTyName "b"
    r <- freshTyName "r"
    return
        . TyLam () a (Type ())
        . TyLam () b (Type ())
        . TyForall () r (Type ())
        . TyFun () (TyFun () (TyVar () a) $ TyVar () r)
        . TyFun () (TyFun () (TyVar () b) $ TyVar () r)
        $ TyVar () r

-- | 'Left' as a PLC term.
--
-- > /\(a b :: *) -> \(x : a) -> /\(r :: *) -> \(f : a -> r) -> (g : b -> r) -> f x
left :: TermLike term TyName Name uni fun => term ()
left = runQuote $ do
    a <- freshTyName "a"
    b <- freshTyName "b"
    x <- freshName "x"
    r <- freshTyName "r"
    f <- freshName "f"
    g <- freshName "g"
    return
        . tyAbs  () a (Type ())
        . tyAbs  () b (Type ())
        . lamAbs () x (TyVar () a)
        . tyAbs  () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) $ TyVar () r)
        . lamAbs () g (TyFun () (TyVar () b) $ TyVar () r)
        . apply  () (var () f)
        $ var    () x

-- | 'Right' as a PLC term.
--
-- > /\(a b :: *) -> \(y : b) -> /\(r :: *) -> \(f : a -> r) -> (g : b -> r) -> g y
right :: TermLike term TyName Name uni fun => term ()
right = runQuote $ do
    a <- freshTyName "a"
    b <- freshTyName "b"
    y <- freshName "y"
    r <- freshTyName "r"
    f <- freshName "f"
    g <- freshName "g"
    return
        . tyAbs  () a (Type ())
        . tyAbs  () b (Type ())
        . lamAbs () y (TyVar () b)
        . tyAbs  () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) $ TyVar () r)
        . lamAbs () g (TyFun () (TyVar () b) $ TyVar () r)
        . apply  () (var () g)
        $ var    () y
