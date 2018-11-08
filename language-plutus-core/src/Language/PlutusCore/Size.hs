module Language.PlutusCore.Size ( sizeTerm
                                ) where

import           Data.Functor.Foldable
import           Language.PlutusCore.Type

sizeTerm :: Integral b => Term tyname name a -> b
sizeTerm = cata a where
    a VarF{}            = 1
    a (TyAbsF _ _ _ t)  = 1 + t
    a (LamAbsF _ _ _ t) = 1 + t
    a (ApplyF _ t t')   = 1 + t + t'
    a ConstantF{}       = 1
    a (TyInstF _ t _)   = 1 + t
    a (UnwrapF _ t)     = 1 + t
    a (WrapF _ _ _ t)   = 1 + t
    a ErrorF{}          = 1
