{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Type
    ( Term (..)
    , termSubterms
    , termSubtermsDeep
    , termSubtypes
    , termSubtypesDeep
    , termVars
    , termTyBinds
    , termBinds
    , Value
    , Type (..)
    , typeSubtypes
    , typeSubtypesDeep
    , typeTyVars
    , typeTyBinds
    , Kind (..)
    , Program (..)
    , Constant (..)
    , Builtin (..)
    , BuiltinName (..)
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
    , TypeBuiltin (..)
    , Gas (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    , KindF (..)
    -- * Helper functions
    , tyLoc
    , termLoc
    -- * Normalized
    , Normalized (..)
    -- * HasUniques
    , type HasUniques
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name

import           Control.Lens
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import           Instances.TH.Lift              ()
import           GHC.Exts (Constraint)
import           Language.Haskell.TH.Syntax     (Lift)

newtype Gas = Gas
    { unGas :: Natural
    }

{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

-- | ann 'Type' assigned to expressions.
data Type tyname ann
    = TyVar ann (tyname ann)
    | TyFun ann (Type tyname ann) (Type tyname ann)
    | TyIFix ann (Type tyname ann) (Type tyname ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyBuiltin ann TypeBuiltin -- ^ Builtin type
    | TyLam ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyApp ann (Type tyname ann) (Type tyname ann)
    deriving (Functor, Show, Generic, NFData, Lift)

data TypeF tyname ann x
    = TyVarF ann (tyname ann)
    | TyFunF ann x x
    | TyIFixF ann x x
    | TyForallF ann (tyname ann) (Kind ann) x
    | TyBuiltinF ann TypeBuiltin
    | TyLamF ann (tyname ann) (Kind ann) x
    | TyAppF ann x x
    deriving (Functor, Traversable, Foldable)

type instance Base (Type tyname ann) = TypeF tyname ann

instance Recursive (Type tyname ann) where
    project (TyVar ann tn)         = TyVarF ann tn
    project (TyFun ann ty ty')     = TyFunF ann ty ty'
    project (TyIFix ann pat arg)   = TyIFixF ann pat arg
    project (TyForall ann tn k ty) = TyForallF ann tn k ty
    project (TyBuiltin ann b)      = TyBuiltinF ann b
    project (TyLam ann tn k ty)    = TyLamF ann tn k ty
    project (TyApp ann ty ty')     = TyAppF ann ty ty'

instance Corecursive (Type tyname ann) where
    embed (TyVarF ann tn)         = TyVar ann tn
    embed (TyFunF ann ty ty')     = TyFun ann ty ty'
    embed (TyIFixF ann pat arg)   = TyIFix ann pat arg
    embed (TyForallF ann tn k ty) = TyForall ann tn k ty
    embed (TyBuiltinF ann b)      = TyBuiltin ann b
    embed (TyLamF ann tn k ty)    = TyLam ann tn k ty
    embed (TyAppF ann ty ty')     = TyApp ann ty ty'

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname ann) (Type tyname ann)
typeSubtypes f = \case
    TyFun ann ty1 ty2 -> TyFun ann <$> f ty1 <*> f ty2
    TyIFix ann pat arg -> TyIFix ann <$> f pat <*> f arg
    TyForall ann tn k ty -> TyForall ann tn k <$> f ty
    TyLam ann tn k ty -> TyLam ann tn k <$> f ty
    TyApp ann ty1 ty2 -> TyApp ann <$> f ty1 <*> f ty2
    b@TyBuiltin {} -> pure b
    v@TyVar {} -> pure v

-- | Get all the transitive child 'Type's of the given 'Type'.
typeSubtypesDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Type tyname ann) (Type tyname ann)
typeSubtypesDeep = cosmosOf typeSubtypes

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname ann) (tyname ann)
typeTyVars f = \case
    TyVar ann n -> TyVar ann <$> f n
    x -> pure x

-- | Get all the direct child 'tyname a's of the given 'Type' from binders.
typeTyBinds :: Traversal' (Type tyname ann) (tyname ann)
typeTyBinds f = \case
    TyForall ann tn k ty -> f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty -> f tn <&> \tn' -> TyLam ann tn' k ty
    x -> pure x

tyLoc :: Type tyname ann -> ann
tyLoc (TyVar ann _)        = ann
tyLoc (TyFun ann _ _)      = ann
tyLoc (TyIFix ann _ _)     = ann
tyLoc (TyForall ann _ _ _) = ann
tyLoc (TyBuiltin ann _)    = ann
tyLoc (TyLam ann _ _ _)    = ann
tyLoc (TyApp ann _ _)      = ann

termLoc :: Term tyname name ann -> ann
termLoc (Var ann _)        = ann
termLoc (TyAbs ann _ _ _)  = ann
termLoc (Apply ann _ _)    = ann
termLoc (Constant ann _)   = ann
termLoc (Builtin ann _)    = ann
termLoc (TyInst ann _ _)   = ann
termLoc (Unwrap ann _)     = ann
termLoc (IWrap ann _ _ _)  = ann
termLoc (Error ann _ )     = ann
termLoc (LamAbs ann _ _ _) = ann

data Builtin ann
    = BuiltinName ann BuiltinName
    | DynBuiltinName ann DynamicBuiltinName
    deriving (Functor, Show, Generic, NFData, Lift)

-- See Note [Annotations and equality].
instance Eq (Builtin ann) where
    BuiltinName    _ name1 == BuiltinName    _ name2 = name1 == name2
    DynBuiltinName _ name1 == DynBuiltinName _ name2 = name1 == name2
    BuiltinName    {} == _ = False
    DynBuiltinName {} == _ = False

-- | A constant value.
data Constant ann
    = BuiltinInt ann Integer
    | BuiltinBS ann BSL.ByteString
    | BuiltinStr ann String
    deriving (Functor, Show, Generic, NFData, Lift)

-- See Note [Annotations and equality].
instance Eq (Constant ann) where
    BuiltinInt _ int1 == BuiltinInt _ int2 = int1 == int2
    BuiltinBS _  bs1  == BuiltinBS  _ bs2  = bs1 == bs2
    BuiltinStr _ str1 == BuiltinStr _ str2 = str1 == str2
    BuiltinInt {} == _ = False
    BuiltinBS  {} == _ = False
    BuiltinStr {} == _ = False

-- | A 'Term' is a value.
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
    deriving (Functor, Show, Generic, NFData, Lift)

data TermF tyname name ann x
    = VarF ann (name ann)
    | TyAbsF ann (tyname ann) (Kind ann) x
    | LamAbsF ann (name ann) (Type tyname ann) x
    | ApplyF ann x x
    | ConstantF ann (Constant ann)
    | BuiltinF ann (Builtin ann)
    | TyInstF ann x (Type tyname ann)
    | UnwrapF ann x
    | IWrapF ann (Type tyname ann) (Type tyname ann) x
    | ErrorF ann (Type tyname ann)
    deriving (Functor, Traversable, Foldable)

type instance Base (Term tyname name ann) = TermF tyname name ann

type Value = Term

instance Recursive (Term tyname name ann) where
    project (Var ann n)           = VarF ann n
    project (TyAbs ann n k t)     = TyAbsF ann n k t
    project (LamAbs ann n ty t)   = LamAbsF ann n ty t
    project (Apply ann t t')      = ApplyF ann t t'
    project (Constant ann c)      = ConstantF ann c
    project (Builtin ann bi)      = BuiltinF ann bi
    project (TyInst ann t ty)     = TyInstF ann t ty
    project (Unwrap ann t)        = UnwrapF ann t
    project (IWrap ann pat arg t) = IWrapF ann pat arg t
    project (Error ann ty)        = ErrorF ann ty

instance Corecursive (Term tyname name ann) where
    embed (VarF ann n)           = Var ann n
    embed (TyAbsF ann n k t)     = TyAbs ann n k t
    embed (LamAbsF ann n ty t)   = LamAbs ann n ty t
    embed (ApplyF ann t t')      = Apply ann t t'
    embed (ConstantF ann c)      = Constant ann c
    embed (BuiltinF ann bi)      = Builtin ann bi
    embed (TyInstF ann t ty)     = TyInst ann t ty
    embed (UnwrapF ann t)        = Unwrap ann t
    embed (IWrapF ann pat arg t) = IWrap ann pat arg t
    embed (ErrorF ann ty)        = Error ann ty

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name ann) (Term tyname name ann)
termSubterms f = \case
    LamAbs ann n ty t -> LamAbs ann n ty <$> f t
    TyInst ann t ty -> TyInst ann <$> f t <*> pure ty
    IWrap ann ty1 ty2 t -> IWrap ann ty1 ty2 <$> f t
    TyAbs ann n k t -> TyAbs ann n k <$> f t
    Apply ann t1 t2 -> Apply ann <$> f t1 <*> f t2
    Unwrap ann t -> Unwrap ann <$> f t
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Term tyname name ann) (Term tyname name ann)
termSubtermsDeep = cosmosOf termSubterms

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name ann) (Type tyname ann)
termSubtypes f = \case
    LamAbs ann n ty t -> LamAbs ann n <$> f ty <*> pure t
    TyInst ann t ty -> TyInst ann t <$> f ty
    IWrap ann ty1 ty2 t -> IWrap ann <$> f ty1 <*> f ty2 <*> pure t
    Error ann ty -> Error ann <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Term tyname name ann) (Type tyname ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name ann) (name ann)
termVars f = \case
    Var ann n -> Var ann <$> f n
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'TyAbs'es.
termTyBinds :: Traversal' (Term tyname name ann) (tyname ann)
termTyBinds f = \case
    TyAbs ann tn k t -> f tn <&> \tn' -> TyAbs ann tn' k t
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term tyname name ann) (name ann)
termBinds f = \case
    LamAbs ann n ty t -> f n <&> \n' -> LamAbs ann n' ty t
    x -> pure x

-- | Kinds. Each type has an associated kind.
data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Functor, Show, Generic, NFData, Lift)

data KindF ann x
    = TypeF ann
    | KindArrowF ann x x
    deriving (Functor)

-- See Note [Annotations and equality].
instance Eq (Kind ann) where
    Type _                == Type   _              = True
    KindArrow _ dom1 cod1 == KindArrow _ dom2 cod2 = dom1 == dom2 && cod1 == cod2
    Type{}      == _ = False
    KindArrow{} == _ = False

type instance Base (Kind ann) = KindF ann

instance Recursive (Kind ann) where
    project (Type ann)           = TypeF ann
    project (KindArrow ann k k') = KindArrowF ann k k'

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name ann = Program ann (Version ann) (Term tyname name ann)
    deriving (Show, Functor, Generic, NFData, Lift)

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype NFData
      deriving Applicative via Identity

deriving newtype instance PrettyBy config a => PrettyBy config (Normalized a)

-- | All kinds of uniques an entity contains.
type family HasUniques a :: Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname ann) = HasUnique (tyname ann) TypeUnique
type instance HasUniques (Term tyname name ann) =
    (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
type instance HasUniques (Program tyname name ann) = HasUniques (Term tyname name ann)
