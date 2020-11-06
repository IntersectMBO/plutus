module Language.PlutusCore.Size
    ( termSize
    , typeSize
    , kindSize
    , programSize
    , serialisedSize
    ) where

import           Language.PlutusCore.Core

import           Codec.Serialise
import qualified Data.ByteString.Lazy     as BSL
import           Data.Functor.Foldable

-- | Count the number of AST nodes in a kind.
kindSize :: Kind a -> Integer
kindSize = cata a where
    a TypeF{}             = 1
    a (KindArrowF _ k k') = 1 + k + k'

-- | Count the number of AST nodes in a type.
typeSize :: Type tyname uni ann -> Integer
typeSize = cata a where
    a TyVarF{}             = 1
    a (TyFunF _ ty ty')    = 1 + ty + ty'
    a (TyIFixF _ ty ty')   = 1 + ty + ty'
    a (TyForallF _ _ k ty) = 1 + kindSize k + ty
    a TyBuiltinF{}         = 1
    a (TyLamF _ _ k ty)    = 1 + kindSize k + ty
    a (TyAppF _ ty ty')    = 1 + ty + ty'

-- | Count the number of AST nodes in a term.
termSize :: Term tyname name uni fun ann -> Integer
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

-- | Count the number of AST nodes in a program.
programSize :: Program tyname name uni fun ann -> Integer
programSize (Program _ _ t) = termSize t

-- | Compute the size of the serializabled form of a value.
serialisedSize :: Serialise a => a -> Integer
serialisedSize = fromIntegral . BSL.length . serialise
