module PlutusIR.Subst
    ( uniquesTerm
    , uniquesType
    ) where

import qualified PlutusCore.Core.Type as PLC
import qualified PlutusCore.Name      as PLC
import           PlutusCore.Subst     (uniquesType)

import           PlutusIR.Core

import           Control.Lens
import           Data.Set             as Set
import           Data.Set.Lens        (setOf)

uniquesTerm
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Term tyname name uni fun ann -> Set PLC.Unique
uniquesTerm = setOf termUniquesDeep
