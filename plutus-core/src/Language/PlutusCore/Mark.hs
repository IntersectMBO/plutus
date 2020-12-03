module Language.PlutusCore.Mark
    ( markNonFreshTerm
    , markNonFreshType
    , markNonFreshProgram
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | Marks all the 'Unique's in a type as used, so they will not be generated in future. Useful if you
-- have a type which was not generated in 'Quote'.
markNonFreshType
    :: (HasUniques (Type tyname uni ann), MonadQuote m)
    => Type tyname uni ann -> m ()
markNonFreshType = markNonFreshMax . uniquesType

-- | Marks all the 'Unique's in a term as used, so they will not be generated in future. Useful if you
-- have a term which was not generated in 'Quote'.
markNonFreshTerm
    :: (HasUniques (Term tyname name uni fun ann), MonadQuote m)
    => Term tyname name uni fun ann -> m ()
markNonFreshTerm = markNonFreshMax . uniquesTerm

-- | Marks all the 'Unique's in a program as used, so they will not be generated in future. Useful if you
-- have a program which was not generated in 'Quote'.
markNonFreshProgram
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, MonadQuote m)
    => Program tyname name uni fun ann
    -> m ()
markNonFreshProgram (Program _ _ body) = markNonFreshTerm body
