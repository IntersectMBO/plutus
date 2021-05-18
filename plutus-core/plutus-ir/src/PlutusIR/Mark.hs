module PlutusIR.Mark
    ( markNonFreshTerm
    , markNonFreshType
    , markNonFreshProgram
    ) where

import qualified PlutusCore.Core  as PLC
import qualified PlutusCore.Name  as PLC

import           PlutusCore.Quote

import           PlutusIR.Core
import           PlutusIR.Subst

-- | Marks all the 'Unique's in a term as used, so they will not be generated in future. Useful if you
-- have a term which was not generated in 'Quote'.
markNonFreshTerm
    :: (PLC.HasUniques (Term tyname name uni fun ann), MonadQuote m)
    => Term tyname name uni fun ann -> m ()
markNonFreshTerm = markNonFreshMax . uniquesTerm

-- | Marks all the 'Unique's in a type as used, so they will not be generated in future. Useful if you
-- have a type which was not generated in 'Quote'.
markNonFreshType
    :: (PLC.HasUniques (Type tyname uni ann), MonadQuote m)
    => Type tyname uni ann -> m ()
markNonFreshType = markNonFreshMax . uniquesType

-- | Marks all the 'Unique's in a program as used, so they will not be generated in future. Useful if you
-- have a program which was not generated in 'Quote'.
markNonFreshProgram
    :: (PLC.HasUniques (Program tyname name uni fun ann), MonadQuote m)
    => Program tyname name uni fun ann
    -> m ()
markNonFreshProgram (Program _ body) = markNonFreshTerm body
