{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Language.PlutusCore.Merkle.Size
    ( termSize
    , typeSize
    , kindSize
    , programSize
    , programNumTypeNodes
    , programNumTermNodes
    , programNumNames
    , astInfo
    , serialisedSize
    ) where

import           Language.PlutusCore.Merkle.Type

import           Codec.Serialise
import qualified Data.ByteString.Lazy            as BSL
import           Data.Functor.Foldable

-- | Count the number of AST nodes in a kind.
kindSize :: Kind a -> Integer
kindSize = cata a where
    a TypeF{}             = 1
    a (KindArrowF _ k k') = 1 + k + k'

-- | Count the total number of AST nodes in a type (excluding names)
typeSize :: Type tyname ann -> Integer
typeSize = cata a where
    a TyVarF{}             = 1
    a (TyFunF _ ty ty')    = 1 + ty + ty'
    a (TyIFixF _ ty ty')   = 1 + ty + ty'
    a (TyForallF _ _ k ty) = 1 + kindSize k + ty
    a TyBuiltinF{}         = 1
    a (TyLamF _ _ k ty)    = 1 + kindSize k + ty
    a (TyAppF _ ty ty')    = 1 + ty + ty'
    a (TyPrunedF _ _ )     = 1

-- | Count the number of AST nodes in a term.
termSize :: Term tyname name ann -> Integer
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
    a (PruneF _ _)        = 1

-- | Count the number of AST nodes in a program.
programSize :: Program tyname name ann -> Integer
programSize (Program _ _ t) = termSize t


-- | Count the number of nodes involved in types, including kinds

termNumTypeNodes :: Term tyname name ann -> Integer
termNumTypeNodes = cata a where
    a VarF{}              = 0
    a (TyAbsF _ _ k t)    = kindSize k + t
    a (ApplyF _ t t')     = t + t'
    a (LamAbsF _ _ ty t)  = typeSize ty + t
    a ConstantF{}         = 0 -- really?
    a BuiltinF{}          = 0 -- really?
    a (TyInstF _ t ty)    = t + typeSize ty
    a (UnwrapF _ t)       = t
    a (IWrapF _ ty ty' t) = typeSize ty + typeSize ty' + t
    a (ErrorF _ ty)       = typeSize ty
    a (PruneF _ _)        = 0

-- | Count the number of AST nodes in a program.
programNumTypeNodes :: Program tyname name ann -> Integer
programNumTypeNodes (Program _ _ t) = termNumTypeNodes t


-- | Count the number of names in types/terms/programs

typeNumNames :: Type tyname ann -> Integer
typeNumNames = cata a where
    a TyVarF{}             = 1
    a (TyFunF _ ty ty')    = ty + ty'
    a (TyIFixF _ ty ty')   = ty + ty'
    a (TyForallF _ _ _ ty) = 1 + ty
    a TyBuiltinF{}         = 0 -- really?
    a (TyLamF _ _ _ ty)    = 1 + ty
    a (TyAppF _ ty ty')    = 1 + ty + ty'
    a (TyPrunedF _ _ )     = 1

termNumNames :: Term tyname name ann -> Integer
termNumNames = cata a where
    a VarF{}              = 1
    a (TyAbsF _ _ _ t)    = 1 + t
    a (ApplyF _ t t')     = t + t'
    a (LamAbsF _ _ ty t)  = 1 + typeNumNames ty + t
    a ConstantF{}         = 0 -- really?
    a BuiltinF{}          = 0 -- really?
    a (TyInstF _ t ty)    = t + typeNumNames ty
    a (UnwrapF _ t)       = t
    a (IWrapF _ ty ty' t) = typeNumNames ty + typeNumNames ty' + t
    a (ErrorF _ ty)       = typeNumNames ty
    a (PruneF _ _)        = 0

programNumNames :: Program tyname name ann -> Integer
programNumNames (Program _ _ t) = termNumNames t


-- | Count the number of AST nodes in a term.
termNumTermNodes :: Term tyname name ann -> Integer
termNumTermNodes = cata a where
    a VarF{}            = 1
    a (TyAbsF _ _ _ t)  = 1 + t
    a (ApplyF _ t t')   = 1 + t + t'
    a (LamAbsF _ _ _ t) = 1 + t
    a ConstantF{}       = 1
    a BuiltinF{}        = 1
    a (TyInstF _ t _)   = 1 + t
    a (UnwrapF _ t)     = 1 + t
    a (IWrapF _ _ _  t) = 1 + t
    a ErrorF{}          = 1
    a PruneF{}          = 1

programNumTermNodes :: Program tyname name ann -> Integer
programNumTermNodes (Program _ _ t) = termNumTermNodes t

-- We could have a single function to collect all of these numbers,
-- but this was quicker.

data ASTinfo = ASTinfo {
      numNodes     :: Integer,
      numTypeNodes :: Integer,
      numTermNodes :: Integer,
      numNames     :: Integer
    }

instance Show ASTinfo where
    show i = (show $ numNodes i) ++ " nodes ("
             ++ (show $ numTermNodes i) ++ " in terms, "
             ++ (show $ numTypeNodes i) ++ " in types), "
             ++ (show $ numNames i) ++ " names"


astInfo :: Program tyname name ann -> ASTinfo
astInfo p = ASTinfo (programSize p) (programNumTypeNodes p) (programNumTermNodes p) (programNumNames p)



-- | Compute the size of the serializabled form of a value.
serialisedSize :: Serialise a => a -> Integer
serialisedSize = fromIntegral . BSL.length . serialise
