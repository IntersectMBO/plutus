{-# LANGUAGE FlexibleContexts #-}
-- | PlutusIR versions of the functions in Language.PlutusCore.Normalize
module Language.PlutusIR.Normalize
    ( Export.normalizeType
    , normalizeTypesIn
    , normalizeTypesInProgram
    ) where

import           Language.PlutusCore.Core               as PLC (Normalized (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize          as Export (normalizeType)
import           Language.PlutusCore.Normalize.Internal hiding (normalizeTypesInM)
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename             (rename)
import           Language.PlutusIR
import           Language.PlutusIR.Transform.Rename     ()

import           Control.Lens
import           Control.Monad                          ((>=>))

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesIn
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m)
    => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
normalizeTypesIn = rename >=> runNormalizeTypeM . normalizeTypesInM

-- | Normalize every 'Type' in a 'Program'.
normalizeTypesInProgram
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m)
    => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
normalizeTypesInProgram (Program x t) = Program x <$> normalizeTypesIn t

-- | Normalize every 'Type' in a 'Term'.
-- Mirrors the `normalizeTypesInM` of 'Language.PlutusCore.Normalize.Internal', working on PIR.Term instead
normalizeTypesInM
    :: (HasUnique tyname TypeUnique, MonadQuote m)
    => Term tyname name uni fun ann -> NormalizeTypeT m tyname uni ann (Term tyname name uni fun ann)
normalizeTypesInM = transformMOf termSubterms normalizeChildTypes where
    normalizeChildTypes = termSubtypes (fmap unNormalized . normalizeTypeM)
