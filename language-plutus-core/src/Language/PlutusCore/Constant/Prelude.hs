{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant.Prelude
    ( Size
    , getBuiltinUnit
    , getBuiltinUnitval
    , getBuiltinTrue
    , getBuiltinFalse
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

import qualified Data.ByteString as BSL

type Size = Natural

newtype Fresh a = Fresh ()

instance Functor Fresh where
    fmap = undefined
instance Applicative Fresh where
instance Monad Fresh where

freshName :: a -> BSL.ByteString -> Fresh (Name a)
freshName = undefined

freshTyName :: a -> BSL.ByteString -> Fresh (TyName a)
freshTyName = fmap TyName .* freshName

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Fresh (Type TyName ())
getBuiltinUnit = do
    a <- freshTyName () "A"
    return
        . TyForall () a (Type ())
        $ TyFun () (TyVar () a) (TyVar () a)

-- | Church-encoded '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Fresh (Term TyName Name ())
getBuiltinUnitval = do
    a <- freshTyName () "A"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        $ Var () x

-- | Church-encoded 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Fresh (Term TyName Name ())
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
       $ Apply () (Var () x) (undefined builtinUnitval)

-- | Church-encoded 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Fresh (Term TyName Name ())
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
       $ Apply () (Var () y) (undefined builtinUnitval)
