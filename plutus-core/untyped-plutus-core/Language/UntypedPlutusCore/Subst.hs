{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.UntypedPlutusCore.Subst
    ( substVarA
    , substVar
    , termSubstNamesM
    , termSubstNames
    , termSubstFreeNamesA
    , termSubstFreeNames
    , termMapNames
    , programMapNames
    , uniquesTerm
    , vTerm
    ) where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Core        (HasUniques)
import           Language.PlutusCore.Name

import           Control.Lens
import           Data.Set                        as Set

purely :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
purely = coerce

-- | Applicatively replace a variable using the given function.
substVarA
    :: Applicative f
    => (name -> f (Maybe (Term name uni ann)))
    -> Term name uni ann
    -> f (Term name uni ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _     t              = pure t

-- | Replace a variable using the given function.
substVar
    :: (name -> Maybe (Term name uni ann))
    -> Term name uni ann
    -> Term name uni ann
substVar = purely substVarA

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
    :: Monad m
    => (name -> m (Maybe (Term name uni ann)))
    -> Term name uni ann
    -> m (Term name uni ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively substitute names using the given function (i.e. do not substitute binders).
termSubstNames
    :: (name -> Maybe (Term name uni ann))
    -> Term name uni ann
    -> Term name uni ann
termSubstNames = purely termSubstNamesM

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

-- | Completely replace the names with a new name type.
termMapNames
    :: forall name name' uni ann
    . (name -> name')
    -> Term name uni ann
    -> Term name' uni ann
termMapNames f = go
    where
        -- This is all a bit clunky because of the type-changing, I'm not sure of a nicer way to do it
        go :: Term name uni ann -> Term name' uni ann
        go = \case
            LamAbs ann name body -> LamAbs ann (f name) (go body)
            Var ann name -> Var ann (f name)

            Apply ann t1 t2 -> Apply ann (go t1) (go t2)
            Delay ann t -> Delay ann (go t)
            Force ann t -> Force ann (go t)

            Constant ann c -> Constant ann c
            Builtin ann b -> Builtin ann b
            Error ann -> Error ann

programMapNames
    :: forall name name' uni ann
    . (name -> name')
    -> Program name uni ann
    -> Program name' uni ann
programMapNames f (Program a v term) = Program a v (termMapNames f term)

-- All variables

setOf :: Getting (Set a) s a -> s -> Set a
setOf g = foldMapOf g singleton

-- | Get all the term variables in a term.
vTerm :: Ord name => Term name uni ann -> Set name
vTerm = setOf $ termSubtermsDeep . termVars

-- All uniques

-- | Get all the uniques in a term
uniquesTerm :: HasUniques (Term name uni ann) => Term name uni ann -> Set Unique
uniquesTerm = setOf termUniquesDeep


