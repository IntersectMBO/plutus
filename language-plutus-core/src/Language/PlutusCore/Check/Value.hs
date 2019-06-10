{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Check.Value
    ( checkTerm
    , checkProgram
    , isTermValue
    , ValueRestrictionError(..)
    , AsValueRestrictionError(..)
    ) where

import           Language.PlutusCore.Error
import           Language.PlutusCore.Type

import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Data.Either
import           Data.Foldable             (traverse_)
import           Data.Functor.Foldable

-- | Check whether a term satisfies the value restriction.
checkTerm
    :: (AsValueRestrictionError e tyname ann, MonadError e m) => Term tyname name ann -> m ()
checkTerm = para $ \case
    TyAbsF ann name _ (body, rest) -> do
        unless (isTermValue body) $ throwing _ValueRestrictionError $ ValueRestrictionViolation ann name
        rest
    termF                          -> traverse_ snd termF

-- | Check whether a program satisfies the value restriction.
checkProgram
    :: (AsValueRestrictionError e tyname ann, MonadError e m) => Program tyname name ann -> m ()
checkProgram (Program _ _ term) = checkTerm term

isTermValue :: Term tyname name a -> Bool
isTermValue = isRight . termValue

termValue :: Term tyname name a -> Either (NormalizationError tyname name a) ()
termValue (IWrap _ _ _ term) = termValue term
termValue (TyAbs _ _ _ t)    = termValue t
termValue LamAbs {}          = pure ()
termValue Constant {}        = pure ()
termValue t                  = Left $ BadTerm (termLoc t) t "term value"
