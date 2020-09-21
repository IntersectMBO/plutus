module Language.UntypedPlutusCore.Subst
    ( termSubstFreeNamesA
    , termSubstFreeNames
    ) where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Name

import           Control.Lens
import           Data.Set                        as Set

purely :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
purely = coerce

-- | Applicatively substitute *free* names using the given function.
termSubstFreeNamesA
    :: (Applicative f, HasUnique name TermUnique)
    => (name -> f (Maybe (Term name uni ann)))
    -> Term name uni ann
    -> f (Term name uni ann)
termSubstFreeNamesA f = go Set.empty where
    go bvs var@(Var _ name)           =
        if (name ^. unique) `member` bvs
            then pure var
            else fromMaybe var <$> f name
    go bvs (LamAbs ann name body) = LamAbs ann name <$> go (insert (name ^. unique) bvs) body
    go bvs (Apply ann fun arg)    = Apply ann <$> go bvs fun <*> go bvs arg
    go bvs (Delay ann term)       = Delay ann <$> go bvs term
    go bvs (Force ann term)       = Force ann <$> go bvs term
    go _   term@Constant{}        = pure term
    go _   term@Builtin{}         = pure term
    go _   term@Error{}           = pure term

-- | Substitute *free* names using the given function.
termSubstFreeNames
    :: HasUnique name TermUnique
    => (name -> Maybe (Term name uni ann))
    -> Term name uni ann
    -> Term name uni ann
termSubstFreeNames = purely termSubstFreeNamesA
