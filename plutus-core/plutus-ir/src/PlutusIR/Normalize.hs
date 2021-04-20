{-# LANGUAGE FlexibleContexts #-}
-- | PlutusIR versions of the functions in PlutusCore.Normalize
module PlutusIR.Normalize
    ( Export.normalizeType
    , normalizeTypesIn
    , normalizeTypesInProgram
    ) where

import           PlutusCore.Core               as PLC (Normalized (..))
import           PlutusCore.Name
import           PlutusCore.Normalize          as Export (normalizeType)
import           PlutusCore.Normalize.Internal hiding (normalizeTypesInM)
import           PlutusCore.Quote
import           PlutusCore.Rename             (rename)
import           PlutusCore.Universe           (HasUniApply)
import           PlutusIR
import           PlutusIR.Transform.Rename     ()

import           Control.Lens
import           Control.Monad                 ((>=>))

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m, HasUniApply uni)
    => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
normalizeTypesIn = rename >=> runNormalizeTypeM . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program'.
normalizeTypesInProgram
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m, HasUniApply uni)
    => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
normalizeTypesInProgram (Program x t) = Program x <$> normalizeTypesIn t

-- | Normalize every 'Type' in a 'Term'.
-- Mirrors the `normalizeTypesInM` of 'PlutusCore.Normalize.Internal', working on PIR.Term instead
normalizeTypesInM
    :: (HasUnique tyname TypeUnique, MonadQuote m, HasUniApply uni)
    => Term tyname name uni fun ann -> NormalizeTypeT m tyname uni ann (Term tyname name uni fun ann)
normalizeTypesInM = transformMOf termSubterms normalizeChildTypes where
    normalizeChildTypes = termSubtypes (fmap unNormalized . normalizeTypeM)
