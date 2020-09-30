{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}


module Language.PlutusCore.Core.Type
    ( Kind(..)
    , Type(..)
    , BuiltinName(..)
    , StaticBuiltinName(..)
    , DynamicBuiltinName(..)
    , Term(..)
    , Version(..)
    , Program(..)
    , UniOf
    , Normalized(..)
    , HasUniques
    , defaultVersion
    , allStaticBuiltinNames
    -- * Helper functions
    , toTerm
    , termAnn
    , typeAnn
    )
where

import           PlutusPrelude

import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Lens
import           Data.Array                   (Ix)
import           Data.Hashable
import           Data.Text                    (Text)
import           GHC.Exts                     (Constraint)
import           Instances.TH.Lift            ()


{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Show, Functor, Generic, NFData, Lift, Hashable)

-- | A 'Type' assigned to expressions.
data Type tyname uni ann
    = TyVar ann tyname
    | TyFun ann (Type tyname uni ann) (Type tyname uni ann)
    | TyIFix ann (Type tyname uni ann) (Type tyname uni ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann tyname (Kind ann) (Type tyname uni ann)
    | TyBuiltin ann (Some (TypeIn uni)) -- ^ Builtin type
    | TyLam ann tyname (Kind ann) (Type tyname uni ann)
    | TyApp ann (Type tyname uni ann) (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Builtin functions
data StaticBuiltinName
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | LessThanInteger
    | LessThanEqInteger
    | GreaterThanInteger
    | GreaterThanEqInteger
    | EqInteger
    | Concatenate
    | TakeByteString
    | DropByteString
    | SHA2
    | SHA3
    | VerifySignature
    | EqByteString
    | LtByteString
    | GtByteString
    | IfThenElse
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix)

-- | The type of dynamic built-in functions. I.e. functions that exist on certain chains and do
-- not exist on others. Each 'DynamicBuiltinName' has an associated type and operational semantics --
-- this allows to type check and evaluate dynamic built-in names just like static ones.
newtype DynamicBuiltinName = DynamicBuiltinName
    { unDynamicBuiltinName :: Text  -- ^ The name of a dynamic built-in name.
    } deriving (Show, Eq, Ord, Generic)
      deriving newtype (NFData, Hashable)

data BuiltinName
    = StaticBuiltinName StaticBuiltinName
    | DynBuiltinName DynamicBuiltinName
    deriving (Show, Generic, NFData, Hashable, Eq)

data Term tyname name uni ann
    = Var ann name -- ^ a named variable
    | TyAbs ann tyname (Kind ann) (Term tyname name uni ann)
    | LamAbs ann name (Type tyname uni ann) (Term tyname name uni ann)
    | Apply ann (Term tyname name uni ann) (Term tyname name uni ann)
    | Constant ann (Some (ValueOf uni)) -- ^ a constant term
    | Builtin ann BuiltinName
    | TyInst ann (Term tyname name uni ann) (Type tyname uni ann)
    | Unwrap ann (Term tyname name uni ann)
    | IWrap ann (Type tyname uni ann) (Type tyname uni ann) (Term tyname name uni ann)
    | Error ann (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Version of Plutus Core to be used for the program.
data Version ann
    = Version ann Natural Natural Natural
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name uni ann = Program ann (Version ann) (Term tyname name uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Extract the universe from a type.
type family UniOf a :: * -> *

type instance UniOf (Term tyname name uni ann) = uni

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype (NFData, Pretty, PrettyBy config)
      deriving Applicative via Identity

-- | All kinds of uniques an entity contains.
type family HasUniques a :: Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname uni ann) = HasUnique tyname TypeUnique
type instance HasUniques (Term tyname name uni ann)
    = (HasUnique tyname TypeUnique, HasUnique name TermUnique)
type instance HasUniques (Program tyname name uni ann) = HasUniques
    (Term tyname name uni ann)

-- | The default version of Plutus Core supported by this library.
defaultVersion :: ann -> Version ann
defaultVersion ann = Version ann 1 0 0

-- | The list of all 'BuiltinName's.
allStaticBuiltinNames :: [StaticBuiltinName]
allStaticBuiltinNames = [minBound .. maxBound]
-- The way it's defined ensures that it's enough to add a new built-in to 'BuiltinName' and it'll be
-- automatically handled by tests and other stuff that deals with all built-in names at once.

toTerm :: Program tyname name uni ann -> Term tyname name uni ann
toTerm (Program _ _ term) = term

typeAnn :: Type tyname uni ann -> ann
typeAnn (TyVar ann _       ) = ann
typeAnn (TyFun ann _ _     ) = ann
typeAnn (TyIFix ann _ _    ) = ann
typeAnn (TyForall ann _ _ _) = ann
typeAnn (TyBuiltin ann _   ) = ann
typeAnn (TyLam ann _ _ _   ) = ann
typeAnn (TyApp ann _ _     ) = ann

termAnn :: Term tyname name uni ann -> ann
termAnn (Var ann _       ) = ann
termAnn (TyAbs ann _ _ _ ) = ann
termAnn (Apply ann _ _   ) = ann
termAnn (Constant ann _  ) = ann
termAnn (Builtin  ann _  ) = ann
termAnn (TyInst ann _ _  ) = ann
termAnn (Unwrap ann _    ) = ann
termAnn (IWrap ann _ _ _ ) = ann
termAnn (Error ann _     ) = ann
termAnn (LamAbs ann _ _ _) = ann
