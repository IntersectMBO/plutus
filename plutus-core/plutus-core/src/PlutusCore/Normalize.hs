-- | The user-facing API of the normalizer.
module PlutusCore.Normalize
  ( normalizeType
  , normalizeTypesIn
  , normalizeTypesInProgram
  ) where

import PlutusCore.Core
import PlutusCore.Name.Unique
import PlutusCore.Normalize.Internal
import PlutusCore.Rename

import Control.Monad ((>=>))

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
  :: (HasUnique tyname TypeUnique, MonadNormalizeType uni m)
  => Type tyname uni ann -> m (Normalized (Type tyname uni ann))
normalizeType = rename >=> runNormalizeTypeT . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
  :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadNormalizeType uni m)
  => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
normalizeTypesIn = rename >=> runNormalizeTypeT . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program'.
normalizeTypesInProgram
  :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadNormalizeType uni m)
  => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
normalizeTypesInProgram (Program x v t) = Program x v <$> normalizeTypesIn t
