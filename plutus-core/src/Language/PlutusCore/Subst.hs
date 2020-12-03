module Language.PlutusCore.Subst
    ( substTyVarA
    , substVarA
    , substTyVar
    , substVar
    , termSubstNamesM
    , termSubstTyNamesM
    , typeSubstTyNamesM
    , termSubstNames
    , termSubstTyNames
    , typeSubstTyNames
    , termSubstFreeNamesA
    , termSubstFreeNames
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

import           Control.Lens
import           Data.Set                 as Set

purely :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
purely = coerce

-- | Applicatively replace a type variable using the given function.
substTyVarA
    :: Applicative f
    => (tyname -> f (Maybe (Type tyname uni ann)))
    -> Type tyname uni ann
    -> f (Type tyname uni ann)
substTyVarA tynameF ty@(TyVar _ tyname) = fromMaybe ty <$> tynameF tyname
substTyVarA _       ty                  = pure ty

-- | Applicatively replace a variable using the given function.
substVarA
    :: Applicative f
    => (name -> f (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> f (Term tyname name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _     t              = pure t

-- | Replace a type variable using the given function.
substTyVar
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Type tyname uni ann
    -> Type tyname uni ann
substTyVar = purely substTyVarA

-- | Replace a variable using the given function.
substVar
    :: (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
substVar = purely substVarA

-- | Naively monadically substitute type names (i.e. do not substitute binders).
typeSubstTyNamesM
    :: Monad m
    => (tyname -> m (Maybe (Type tyname uni ann)))
    -> Type tyname uni ann
    -> m (Type tyname uni ann)
typeSubstTyNamesM = transformMOf typeSubtypes . substTyVarA

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
    :: Monad m
    => (name -> m (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively monadically substitute type names using the given function (i.e. do not substitute binders).
termSubstTyNamesM
    :: Monad m
    => (tyname -> m (Maybe (Type tyname uni ann)))
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termSubstTyNamesM =
    transformMOf termSubterms . traverseOf termSubtypes . transformMOf typeSubtypes . substTyVarA

-- | Naively substitute type names (i.e. do not substitute binders).
typeSubstTyNames
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Type tyname uni ann
    -> Type tyname uni ann
typeSubstTyNames = purely typeSubstTyNamesM

-- | Naively substitute names using the given function (i.e. do not substitute binders).
termSubstNames
    :: (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstNames = purely termSubstNamesM

-- | Naively substitute type names using the given function (i.e. do not substitute binders).
termSubstTyNames
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstTyNames = purely termSubstTyNamesM

-- | Applicatively substitute *free* names using the given function.
termSubstFreeNamesA
    :: (Applicative f, HasUnique name TermUnique)
    => (name -> f (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> f (Term tyname name uni fun ann)
termSubstFreeNamesA f = go Set.empty where
    go bvs var@(Var _ name)           =
        if (name ^. unique) `member` bvs
            then pure var
            else fromMaybe var <$> f name
    go bvs (TyAbs ann name kind body) = TyAbs ann name kind <$> go bvs body
    go bvs (LamAbs ann name ty body)  = LamAbs ann name ty <$> go (insert (name ^. unique) bvs) body
    go bvs (Apply ann fun arg)        = Apply ann <$> go bvs fun <*> go bvs arg
    go bvs (TyInst ann term ty)       = go bvs term <&> \term' -> TyInst ann term' ty
    go bvs (Unwrap ann term)          = Unwrap ann <$> go bvs term
    go bvs (IWrap ann pat arg term)   = IWrap ann pat arg <$> go bvs term
    go _   term@Constant{}            = pure term
    go _   term@Builtin{}             = pure term
    go _   term@Error{}               = pure term

-- | Substitute *free* names using the given function.
termSubstFreeNames
    :: HasUnique name TermUnique
    => (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstFreeNames = purely termSubstFreeNamesA
