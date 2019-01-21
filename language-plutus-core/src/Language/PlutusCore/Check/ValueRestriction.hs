-- | The value restriction check.

{-# LANGUAGE LambdaCase #-}

module Language.PlutusCore.Check.ValueRestriction
    ( checkTerm
    , checkProgram
    ) where

import           Language.PlutusCore.Error
import           Language.PlutusCore.Type
import           Language.PlutusCore.View  (isTermValue)

import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Data.Foldable             (traverse_)
import           Data.Functor.Foldable

-- | Check whether a term satisfies the value restriction.
checkTerm
    :: (AsValueRestrictionError e tyname ann, MonadError e m) => Term tyname name ann -> m ()
checkTerm = para $ \case
    TyAbsF ann name _ (body, rest) -> do
        unless (isTermValue body) $
            throwing _ValueRestrictionError $ ValueRestrictionViolation ann name
        rest
    termF                          -> traverse_ snd termF

-- | Check whether a program satisfies the value restriction.
checkProgram
    :: (AsValueRestrictionError e tyname ann, MonadError e m) => Program tyname name ann -> m ()
checkProgram (Program _ _ term) = checkTerm term
