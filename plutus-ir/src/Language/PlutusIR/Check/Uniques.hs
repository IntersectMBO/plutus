module Language.PlutusIR.Check.Uniques where

import           Language.PlutusIR
import qualified Language.PlutusIR.Analysis.Dependencies as Deps
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Name                as PLC
import qualified Language.PlutusCore.Analysis.Definitions                as PLC

import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE

type Scope = NE.NonEmpty (Set.Set PLC.Unique)
