-- | The user-facing API of the normalizer.

module Language.PlutusCore.Normalize
    ( normalizeType
    , normalizeTypeFull
    , normalizeTypeGas
    , normalizeTypesIn
    , normalizeTypesFullIn
    , normalizeTypesGasIn
    , normalizeTypesFullInProgram
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize.Internal
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename

import           Control.Monad                          ((>=>))

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => m () -> Type tyname uni ann -> m (Normalized (Type tyname uni ann))
normalizeType countStep = rename >=> runNormalizeTypeM countStep . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type' without dealing with gas.
normalizeTypeFull
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname uni ann -> m (Normalized (Type tyname uni ann))
normalizeTypeFull = normalizeType $ pure ()

-- | Normalize a 'Type' in the gas-consuming way.
-- Count a single substitution step by subtracting @1@ from available gas or
-- fail when there is no available gas.
normalizeTypeGas
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Gas -> Type tyname uni ann -> m (Maybe (Normalized (Type tyname uni ann)))
normalizeTypeGas gas = rename >=> runNormalizeTypeGasM gas . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => m () -> Term tyname name uni ann -> m (Term tyname name uni ann)
normalizeTypesIn countStep = rename >=> runNormalizeTypeM countStep . normalizeTypesInM

-- | Normalize every 'Type' in a 'Term' without dealing with gas.
normalizeTypesFullIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Term tyname name uni ann -> m (Term tyname name uni ann)
normalizeTypesFullIn = normalizeTypesIn $ pure ()

-- | Normalize every 'Type' in a 'Term' in the gas-consuming way.
-- Count a single substitution step by subtracting @1@ from available gas or
-- fail when there is no available gas.
normalizeTypesGasIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Gas -> Term tyname name uni ann -> m (Maybe (Term tyname name uni ann))
normalizeTypesGasIn gas = rename >=> runNormalizeTypeGasM gas . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program' without dealing with gas.
normalizeTypesFullInProgram
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Program tyname name uni ann -> m (Program tyname name uni ann)
normalizeTypesFullInProgram (Program x v t) = Program x v <$> normalizeTypesFullIn t
