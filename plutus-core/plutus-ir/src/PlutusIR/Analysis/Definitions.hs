{-# LANGUAGE LambdaCase #-}
-- | Definition analysis for Plutus IR.
-- This just adapts term-related code from PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module PlutusIR.Analysis.Definitions
    ( UniqueInfos
    , termDefs
    , typeDefs
    , runTermDefs
    , runTypeDefs
    ) where

import Data.Functor.Foldable
import PlutusCore.Core (TypeF (TyForallF, TyLamF, TyVarF))
import PlutusCore.Error
import PlutusCore.Name
import PlutusIR.Core
import PlutusIR.Core.Instance.Recursive (TermF (IWrapF, LamAbsF, TyAbsF, TyInstF, VarF))

import Control.Monad.State
import Control.Monad.Writer

import PlutusCore.Analysis.Definitions (ScopeType (TermScope, TypeScope), UniqueInfos, addDef,
                                        addUsage)

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term tyname name uni fun ann
    -> m ()
termDefs = cata $ \case
    VarF ann n         -> addUsage n ann TermScope
    LamAbsF ann n ty t -> addDef n ann TermScope >> typeDefs ty >> t
    IWrapF _ pat arg t -> typeDefs pat >> typeDefs arg >> t
    TyAbsF ann tn _ t  -> addDef tn ann TypeScope >> t
    TyInstF _ t ty     -> t >> typeDefs ty
    x                  -> sequence_ x

typeDefs
    :: (Ord ann,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Type tyname uni ann
    -> m ()
typeDefs = cata $ \case
    TyVarF ann n         -> addUsage n ann TypeScope
    TyForallF ann tn _ t -> addDef tn ann TypeScope >> t
    TyLamF ann tn _ t    -> addDef tn ann TypeScope >> t
    x                    -> sequence_ x

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        Monad m)
    => Term tyname name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs

runTypeDefs
    :: (Ord ann,
        HasUnique tyname TypeUnique,
        Monad m)
    => Type tyname uni ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTypeDefs = runWriterT . flip execStateT mempty . typeDefs
