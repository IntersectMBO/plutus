{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeFamilies #-}

module Language.PlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    , TypeF (..)
    , KindF (..)
    ) where

import           Language.PlutusCore.Core.Type

import           Data.Functor.Foldable

data KindF ann x
    = TypeF ann
    | KindArrowF ann x x
    deriving (Functor)

data TypeF tyname ann x
    = TyVarF ann (tyname ann)
    | TyFunF ann x x
    | TyIFixF ann x x
    | TyForallF ann (tyname ann) (Kind ann) x
    | TyBuiltinF ann TypeBuiltin
    | TyLamF ann (tyname ann) (Kind ann) x
    | TyAppF ann x x
    deriving (Functor, Traversable, Foldable)

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

type instance Base (Kind ann) = KindF ann
type instance Base (Type tyname ann) = TypeF tyname ann
type instance Base (Term tyname name ann) = TermF tyname name ann

instance Recursive (Kind ann) where
    project (Type ann)           = TypeF ann
    project (KindArrow ann k k') = KindArrowF ann k k'

instance Corecursive (Kind ann) where
    embed (TypeF ann)           = Type ann
    embed (KindArrowF ann k k') = KindArrow ann k k'

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
