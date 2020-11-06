-- | The user-facing API of the normalizer.

module Language.PlutusCore.Normalize
    ( normalizeType
    , normalizeTypesIn
    , normalizeTypesInProgram
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
    :: (HasUnique tyname TypeUnique, MonadQuote m)
    => Type tyname uni ann -> m (Normalized (Type tyname uni ann))
normalizeType = rename >=> runNormalizeTypeM . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m)
    => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
normalizeTypesIn = rename >=> runNormalizeTypeM . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program'.
normalizeTypesInProgram
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m)
    => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
normalizeTypesInProgram (Program x v t) = Program x v <$> normalizeTypesIn t
