module Language.PlutusCore.Size ( termSize
                                ) where

import           Data.Functor.Foldable
import           Language.PlutusCore.Type

kindSize :: Kind a -> Int
kindSize = cata a where
    a TypeF{}             = 1
    a (KindArrowF _ k k') = 1 + k + k'
    a SizeF{}             = 1

typeSize :: Type tyname a -> Int
typeSize = cata a where
    a TyVarF{}             = 1
    a (TyFunF _ ty ty')    = 1 + ty + ty'
    a (TyIFixF _ ty ty')   = 1 + ty + ty'
    a (TyForallF _ _ k ty) = 1 + kindSize k + ty
    a TyBuiltinF{}         = 1
    a TyIntF{}             = 1
    a (TyLamF _ _ k ty)    = 1 + kindSize k + ty
    a (TyAppF _ ty ty')    = 1 + ty + ty'

-- | This exists so that we can measure term size. It counts the number of AST
-- nodes.
termSize :: Term tyname name a -> Int
termSize = cata a where
    a VarF{}              = 1
    a (TyAbsF _ _ k t)    = 1 + kindSize k + t
    a (ApplyF _ t t')     = 1 + t + t'
    a (LamAbsF _ _ ty t)  = 1 + typeSize ty + t
    a ConstantF{}         = 1
    a BuiltinF{}          = 1
    a (TyInstF _ t ty)    = 1 + t + typeSize ty
    a (UnwrapF _ t)       = 1 + t
    a (IWrapF _ ty ty' t) = 1 + typeSize ty + typeSize ty' + t
    a (ErrorF _ ty)       = 1 + typeSize ty
