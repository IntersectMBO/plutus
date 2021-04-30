{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Core.Type
    ( Kind(..)
    , Type(..)
    , Term(..)
    , Version(..)
    , Program(..)
    , UniOf
    , Normalized(..)
    , HasUniques
    , KnownKind (..)
    , ToKind (..)
    , kindOf
    , defaultVersion
    -- * Helper functions
    , toTerm
    , termAnn
    , typeAnn
    , mapFun
    )
where

import           PlutusPrelude

import           PlutusCore.Name
import           PlutusCore.Universe

import           Control.Lens
import           Data.Hashable
import qualified Data.Kind                as GHC
import           Data.Proxy
import           Instances.TH.Lift        ()
import           Language.Haskell.TH.Lift

{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Show, Functor, Generic, NFData, Lift, Hashable)

-- | A 'Type' assigned to expressions.
data Type tyname (uni :: GHC.Type -> GHC.Type) ann
    = TyVar ann tyname
    | TyFun ann (Type tyname uni ann) (Type tyname uni ann)
    | TyIFix ann (Type tyname uni ann) (Type tyname uni ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann tyname (Kind ann) (Type tyname uni ann)
    | TyBuiltin ann (SomeTypeIn uni) -- ^ Builtin type
    | TyLam ann tyname (Kind ann) (Type tyname uni ann)
    | TyApp ann (Type tyname uni ann) (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

data Term tyname name uni fun ann
    = Var ann name -- ^ a named variable
    | TyAbs ann tyname (Kind ann) (Term tyname name uni fun ann)
    | LamAbs ann name (Type tyname uni ann) (Term tyname name uni fun ann)
    | Apply ann (Term tyname name uni fun ann) (Term tyname name uni fun ann)
    | Constant ann (Some (ValueOf uni)) -- ^ a constant term
    | Builtin ann fun
    | TyInst ann (Term tyname name uni fun ann) (Type tyname uni ann)
    | Unwrap ann (Term tyname name uni fun ann)
    | IWrap ann (Type tyname uni ann) (Type tyname uni ann) (Term tyname name uni fun ann)
    | Error ann (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Version of Plutus Core to be used for the program.
data Version ann
    = Version ann Natural Natural Natural
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name uni fun ann = Program ann (Version ann) (Term tyname name uni fun ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Extract the universe from a type.
type family UniOf a :: GHC.Type -> GHC.Type

type instance UniOf (Term tyname name uni fun ann) = uni

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype (NFData, Pretty, PrettyBy config)
      deriving Applicative via Identity

-- | All kinds of uniques an entity contains.
type family HasUniques a :: GHC.Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname uni ann) = HasUnique tyname TypeUnique
type instance HasUniques (Term tyname name uni fun ann) =
    (HasUnique tyname TypeUnique, HasUnique name TermUnique)
type instance HasUniques (Program tyname name uni fun ann) =
    HasUniques (Term tyname name uni fun ann)

-- | A class for converting Haskell kinds to PLC kinds.
class KnownKind kind where
    knownKind :: proxy kind -> Kind ()

instance KnownKind GHC.Type where
    knownKind _ = Type ()

instance (KnownKind dom, KnownKind cod) => KnownKind (dom -> cod) where
    knownKind _ = KindArrow () (knownKind $ Proxy @dom) (knownKind $ Proxy @cod)

-- | For getting the kind of a thing from the universe.
class ToKind (uni :: GHC.Type -> GHC.Type) where
    toKind :: forall k (a :: k). uni (T a) -> Kind ()

-- | Get the PLC kind of @a@.
kindOf :: forall uni k (a :: k). KnownKind k => uni (T a) -> Kind ()
kindOf _ = knownKind $ Proxy @k

-- | The default version of Plutus Core supported by this library.
defaultVersion :: ann -> Version ann
defaultVersion ann = Version ann 1 0 0

toTerm :: Program tyname name uni fun ann -> Term tyname name uni fun ann
toTerm (Program _ _ term) = term

typeAnn :: Type tyname uni ann -> ann
typeAnn (TyVar ann _       ) = ann
typeAnn (TyFun ann _ _     ) = ann
typeAnn (TyIFix ann _ _    ) = ann
typeAnn (TyForall ann _ _ _) = ann
typeAnn (TyBuiltin ann _   ) = ann
typeAnn (TyLam ann _ _ _   ) = ann
typeAnn (TyApp ann _ _     ) = ann

termAnn :: Term tyname name uni fun ann -> ann
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

-- | Map a function over the set of built-in functions.
mapFun :: (fun -> fun') -> Term tyname name uni fun ann -> Term tyname name uni fun' ann
mapFun f = go where
    go (LamAbs ann name ty body)  = LamAbs ann name ty (go body)
    go (TyAbs ann name kind body) = TyAbs ann name kind (go body)
    go (IWrap ann pat arg term)   = IWrap ann pat arg (go term)
    go (Apply ann fun arg)        = Apply ann (go fun) (go arg)
    go (Unwrap ann term)          = Unwrap ann (go term)
    go (Error ann ty)             = Error ann ty
    go (TyInst ann term ty)       = TyInst ann (go term) ty
    go (Var ann name)             = Var ann name
    go (Constant ann con)         = Constant ann con
    go (Builtin ann fun)          = Builtin ann (f fun)
