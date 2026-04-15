{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Transform.Certify.Trace where

import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify

import Control.DeepSeq
import GHC.Generics

data ICSimplifierStage
  = FloatDelay
  | ForceDelay
  | ForceCaseDelay
  | CaseReduce
  | Inline
  | CSE
  | ApplyToCase
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

data NICSimplifierStage
  = CaseOfCase
  | Unknown
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

type SimplifierStage = Either NICSimplifierStage ICSimplifierStage

floatDelayStage
  , forceDelayStage
  , forceCaseDelayStage
  , caseReduceStage
  , inlineStage
  , cseStage
  , applyToCaseStage
  , caseOfCaseStage
  , unknownStage
    :: SimplifierStage
floatDelayStage = Right FloatDelay
forceDelayStage = Right ForceDelay
forceCaseDelayStage = Right ForceCaseDelay
caseReduceStage = Right CaseReduce
inlineStage = Right Inline
cseStage = Right CSE
applyToCaseStage = Right ApplyToCase
caseOfCaseStage = Left CaseOfCase
unknownStage = Left Unknown

data Simplification name uni fun a
  = Simplification
  { beforeAST :: Term name uni fun a
  , stage :: SimplifierStage
  , hints :: Certify.Hints
  , afterAST :: Term name uni fun a
  }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype SimplifierTrace name uni fun a
  = SimplifierTrace
  { simplifierTrace
      :: [Simplification name uni fun a]
  }

initSimplifierTrace :: SimplifierTrace name uni fun a
initSimplifierTrace = SimplifierTrace []

allASTs :: SimplifierTrace name uni fun a -> [Term name uni fun a]
allASTs = \case
  SimplifierTrace [] -> []
  SimplifierTrace xs@(x : _) ->
    -- `SimplifierTrace` is in reverse order: the first item is the last pass run.
    afterAST x : map beforeAST xs
