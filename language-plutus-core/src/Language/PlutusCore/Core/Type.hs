{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Core.Type
    ( Gas(..)
    , Kind(..)
    , TypeBuiltin(..)
    , Type(..)
    , BuiltinName(..)
    , DynamicBuiltinName(..)
    , StagedBuiltinName(..)
    , Builtin(..)
    , Constant(..)
    , Term(..)
    , Value
    , Version(..)
    , Program(..)
    , Normalized(..)
    , HasUniques
    , defaultVersion
    , allBuiltinNames
    -- * Helper functions
    , toTerm
    , termAnn
    , typeAnn
    )
where

import           PlutusPrelude

import           Language.PlutusCore.Name

import           Control.Lens
import qualified Data.ByteString.Lazy       as BSL
import           Data.Hashable
import           Data.Text                  (Text)
import           GHC.Exts                   (Constraint)
import           Instances.TH.Lift          ()
import           Language.Haskell.TH.Syntax (Lift)

{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

newtype Gas = Gas
    { unGas :: Natural
    }

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Functor, Show, Generic, NFData, Lift, Hashable)

-- | A builtin type
data TypeBuiltin
    = TyByteString
    | TyInteger
    | TyString
    deriving (Show, Eq, Ord, Generic, NFData, Lift, Hashable)

-- | A 'Type' assigned to expressions.
data Type tyname ann
    = TyVar ann (tyname ann)
    | TyFun ann (Type tyname ann) (Type tyname ann)
    | TyIFix ann (Type tyname ann) (Type tyname ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyBuiltin ann TypeBuiltin -- ^ Builtin type
    | TyLam ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyApp ann (Type tyname ann) (Type tyname ann)
    deriving (Functor, Show, Generic, NFData, Lift, Hashable)

-- | Builtin functions
data BuiltinName
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
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Lift, Hashable)

-- | The type of dynamic built-in functions. I.e. functions that exist on certain chains and do
-- not exist on others. Each 'DynamicBuiltinName' has an associated type and operational semantics --
-- this allows to type check and evaluate dynamic built-in names just like static ones.
newtype DynamicBuiltinName = DynamicBuiltinName
    { unDynamicBuiltinName :: Text  -- ^ The name of a dynamic built-in name.
    } deriving (Show, Eq, Ord, Generic)
      deriving newtype (NFData, Lift, Hashable)

-- | Either a 'BuiltinName' (known statically) or a 'DynamicBuiltinName' (known dynamically).
data StagedBuiltinName
    = StaticStagedBuiltinName  BuiltinName
    | DynamicStagedBuiltinName DynamicBuiltinName
    deriving (Show, Eq, Generic, NFData, Lift, Hashable)

data Builtin ann
    = BuiltinName ann BuiltinName
    | DynBuiltinName ann DynamicBuiltinName
    deriving (Functor, Show, Generic, NFData, Lift, Hashable)

-- | A constant value.
data Constant ann
    = BuiltinInt ann Integer
    | BuiltinBS ann BSL.ByteString
    | BuiltinStr ann String
    deriving (Functor, Show, Generic, NFData, Lift, Hashable)

data Term tyname name ann
    = Var ann (name ann) -- ^ a named variable
    | TyAbs ann (tyname ann) (Kind ann) (Term tyname name ann)
    | LamAbs ann (name ann) (Type tyname ann) (Term tyname name ann)
    | Apply ann (Term tyname name ann) (Term tyname name ann)
    | Constant ann (Constant ann) -- ^ a constant term
    | Builtin ann (Builtin ann)
    | TyInst ann (Term tyname name ann) (Type tyname ann)
    | Unwrap ann (Term tyname name ann)
    | IWrap ann (Type tyname ann) (Type tyname ann) (Term tyname name ann)
    | Error ann (Type tyname ann)
    deriving (Functor, Show, Generic, NFData, Lift, Hashable)

type Value = Term

-- | Version of Plutus Core to be used for the program.
data Version ann
    = Version ann Natural Natural Natural
    deriving (Show, Functor, Generic, NFData, Lift, Hashable)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name ann = Program ann (Version ann) (Term tyname name ann)
    deriving (Show, Functor, Generic, NFData, Lift, Hashable)

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Lift, Generic)
      deriving newtype NFData
      deriving Applicative via Identity
deriving newtype instance PrettyBy config a => PrettyBy config (Normalized a)

-- | All kinds of uniques an entity contains.
type family HasUniques a :: Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname ann) = HasUnique (tyname ann) TypeUnique
type instance HasUniques (Term tyname name ann)
    = (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
type instance HasUniques (Program tyname name ann) = HasUniques
    (Term tyname name ann)

-- | The default version of Plutus Core supported by this library.
defaultVersion :: ann -> Version ann
defaultVersion ann = Version ann 1 0 0

-- | The list of all 'BuiltinName's.
allBuiltinNames :: [BuiltinName]
allBuiltinNames = [minBound .. maxBound]
-- The way it's defined ensures that it's enough to add a new built-in to 'BuiltinName' and it'll be
-- automatically handled by tests and other stuff that deals with all built-in names at once.

toTerm :: Program tyname name ann -> Term tyname name ann
toTerm (Program _ _ term) = term

typeAnn :: Type tyname ann -> ann
typeAnn (TyVar ann _       ) = ann
typeAnn (TyFun ann _ _     ) = ann
typeAnn (TyIFix ann _ _    ) = ann
typeAnn (TyForall ann _ _ _) = ann
typeAnn (TyBuiltin ann _   ) = ann
typeAnn (TyLam ann _ _ _   ) = ann
typeAnn (TyApp ann _ _     ) = ann

termAnn :: Term tyname name ann -> ann
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
