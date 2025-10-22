-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module UntypedPlutusCore.Subst
    ( substVarA
    , substVar
    , termSubstNamesM
    , termSubstNames
    , termMapNames
    , programMapNames
    , substConstantA
    , substConstant
    , termSubstConstantsM
    , termSubstConstants
    , vTerm
    ) where

import PlutusPrelude

import UntypedPlutusCore.Core

import Control.Lens
import Universe

-- | Applicatively replace a variable using the given function.
substVarA
    :: Applicative f
    => (name -> f (Maybe (Term name uni fun ann)))
    -> Term name uni fun ann
    -> f (Term name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _     t              = pure t

-- | Replace a variable using the given function.
substVar
    :: (name -> Maybe (Term name uni fun ann))
    -> Term name uni fun ann
    -> Term name uni fun ann
substVar = purely substVarA

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
    :: Monad m
    => (name -> m (Maybe (Term name uni fun ann)))
    -> Term name uni fun ann
    -> m (Term name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively substitute names using the given function (i.e. do not substitute binders).
termSubstNames
    :: (name -> Maybe (Term name uni fun ann))
    -> Term name uni fun ann
    -> Term name uni fun ann
termSubstNames = purely termSubstNamesM

-- | Completely replace the names with a new name type.
termMapNames
    :: forall name name' uni fun ann
    . (name -> name')
    -> Term name uni fun ann
    -> Term name' uni fun ann
termMapNames f = go
    where
        -- This is all a bit clunky because of the type-changing, I'm not sure of a nicer way to do it
        go :: Term name uni fun ann -> Term name' uni fun ann
        go = \case
            LamAbs ann name body -> LamAbs ann (f name) (go body)
            Var ann name         -> Var ann (f name)

            Apply ann t1 t2      -> Apply ann (go t1) (go t2)
            Delay ann t          -> Delay ann (go t)
            Force ann t          -> Force ann (go t)
            Constr ann i es      -> Constr ann i (fmap go es)
            Case ann arg cs      -> Case ann (go arg) (fmap go cs)
            Let ann ns t         -> Let ann (fmap f ns) (go t)
            Bind ann t bs        -> Bind ann (go t) (fmap go bs)

            Constant ann c       -> Constant ann c
            Builtin ann b        -> Builtin ann b
            Error ann            -> Error ann

programMapNames
    :: forall name name' uni fun ann
    . (name -> name')
    -> Program name uni fun ann
    -> Program name' uni fun ann
programMapNames f (Program a v term) = Program a v (termMapNames f term)

-- TODO: this could be a Traversal
-- | Get all the term variables in a term.
vTerm :: Fold (Term name uni fun ann) name
vTerm = termSubtermsDeep . termVars

-- | Applicatively replace a constant using the given function.
substConstantA
    :: Applicative f
    => (ann -> Some (ValueOf uni) -> f (Maybe (Term name uni fun ann)))
    -> Term name uni fun ann
    -> f (Term name uni fun ann)
substConstantA valF t@(Constant ann val) = fromMaybe t <$> valF ann val
substConstantA _    t                    = pure t

-- | Replace a constant using the given function.
substConstant
    :: (ann -> Some (ValueOf uni) -> Maybe (Term name uni fun ann))
    -> Term name uni fun ann
    -> Term name uni fun ann
substConstant = purely (substConstantA . curry) . uncurry

-- | Monadically substitute constants using the given function.
termSubstConstantsM
    :: Monad m
    => (ann -> Some (ValueOf uni) -> m (Maybe (Term name uni fun ann)))
    -> Term name uni fun ann
    -> m (Term name uni fun ann)
termSubstConstantsM = transformMOf termSubterms . substConstantA

-- | Substitute constants using the given function.
termSubstConstants
    :: (ann -> Some (ValueOf uni) -> Maybe (Term name uni fun ann))
    -> Term name uni fun ann
    -> Term name uni fun ann
termSubstConstants = purely (termSubstConstantsM . curry) . uncurry
