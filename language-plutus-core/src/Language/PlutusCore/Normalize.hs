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

import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize.Internal
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           Language.PlutusCore.Type

import           Control.Monad                          ((>=>))

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => m () -> Type tyname ann -> m (Normalized (Type tyname ann))
normalizeType countStep = rename >=> runNormalizeTypeM countStep . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type' without dealing with gas.
normalizeTypeFull
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> m (Normalized (Type tyname ann))
normalizeTypeFull = normalizeType $ pure ()

-- | Normalize a 'Type' in the gas-consuming way.
-- Count a single substitution step by subtracting @1@ from available gas or
-- fail when there is no available gas.
normalizeTypeGas
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Gas -> Type tyname ann -> m (Maybe (Normalized (Type tyname ann)))
normalizeTypeGas gas = rename >=> runNormalizeTypeGasM gas . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => m () -> Term tyname name ann -> m (Term tyname name ann)
normalizeTypesIn countStep = rename >=> runNormalizeTypeM countStep . normalizeTypesInM

-- | Normalize every 'Type' in a 'Term' without dealing with gas.
normalizeTypesFullIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Term tyname name ann -> m (Term tyname name ann)
normalizeTypesFullIn = normalizeTypesIn $ pure ()

-- | Same as 'normalizeTypesFullIn' but runs on a 'Program'
normalizeTypesFullInProgram
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Program tyname name ann -> m (Program tyname name ann)
normalizeTypesFullInProgram (Program x v t) = Program x v <$> normalizeTypesFullIn t

-- | Normalize every 'Type' in a 'Term' in the gas-consuming way.
-- Count a single substitution step by subtracting @1@ from available gas or
-- fail when there is no available gas.
normalizeTypesGasIn
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Gas -> Term tyname name ann -> m (Maybe (Term tyname name ann))
normalizeTypesGasIn gas = rename >=> runNormalizeTypeGasM gas . normalizeTypesInM
