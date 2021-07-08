-- | The user-facing API of the normalizer.

module PlutusCore.Normalize
    ( normalizeType
    , normalizeTypesIn
    , normalizeTypesInProgram
    ) where

import           PlutusCore.Core
import           PlutusCore.Name
import           PlutusCore.Normalize.Internal
import           PlutusCore.Quote
import           PlutusCore.Rename

import           Control.Monad                 ((>=>))
import           Universe

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique tyname TypeUnique, MonadQuote m, HasUniApply uni)
    => Type tyname uni ann -> m (Normalized (Type tyname uni ann))
normalizeType = rename >=> runNormalizeTypeM . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m, HasUniApply uni)
    => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
normalizeTypesIn = rename >=> runNormalizeTypeM . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program'.
normalizeTypesInProgram
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m, HasUniApply uni)
    => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
normalizeTypesInProgram (Program x v t) = Program x v <$> normalizeTypesIn t
