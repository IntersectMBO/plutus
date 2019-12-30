{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeFamilies #-}

module Language.PlutusCore.Erasure.Untyped.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    ) where

import           Language.PlutusCore.Erasure.Untyped.Term

import           Data.Functor.Foldable

data TermF name a x
    = VarF a (name a)
    | LamAbsF a (name a) x
    | ApplyF a x x
    | ConstantF a (Constant a)
    | BuiltinF a (Builtin a)
    | ErrorF a
      deriving (Functor, Traversable, Foldable)

type instance Base (Term name a) = TermF name a

instance Recursive (Term name a) where
    project (Var x n)      = VarF x n
    project (LamAbs x n t) = LamAbsF x n t
    project (Apply x t t') = ApplyF x t t'
    project (Constant x c) = ConstantF x c
    project (Builtin x bi) = BuiltinF x bi
    project (Error x)      = ErrorF x

instance Corecursive (Term name a) where
    embed (VarF x n)      = Var x n
    embed (LamAbsF x n t) = LamAbs x n t
    embed (ApplyF x t t') = Apply x t t'
    embed (ConstantF x c) = Constant x c
    embed (BuiltinF x bi) = Builtin x bi
    embed (ErrorF x)      = Error x

