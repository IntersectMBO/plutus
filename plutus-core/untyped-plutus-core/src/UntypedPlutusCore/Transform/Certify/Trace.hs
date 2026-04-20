{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module UntypedPlutusCore.Transform.Certify.Trace where

import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify

import Control.DeepSeq
import GHC.Generics

{-| Datatype which represents optimization passes which are also
certified.

This means that these passes are formalized as part of the certifier,
and adding a new pass constructor to this type means that it is expected
the pass will be also certified in the same PR. -}
data CertifiedOptStage
  = FloatDelay
  | ForceDelay
  | ForceCaseDelay
  | Inline
  | CSE
  | ApplyToCase
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

{-| Datatype which represents optimization passes which are not yet
certified.

IMPORTANT: if you add a new pass, or modify an existing pass, without
also modifying the certifier in the same PR, you must add/move its
corresponding constructor to this type. Please also open an issue
at https://github.com/IntersectMBO/plutus/issues. -}
data UncertifiedOptStage
  = CaseOfCase
  | LetFloatOut
  | CaseReduce
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

type OptStage = Either UncertifiedOptStage CertifiedOptStage

pattern FloatDelayStage :: OptStage
pattern FloatDelayStage = Right FloatDelay

pattern ForceDelayStage :: OptStage
pattern ForceDelayStage = Right ForceDelay

pattern ForceCaseDelayStage :: OptStage
pattern ForceCaseDelayStage = Right ForceCaseDelay

pattern CaseReduceStage :: OptStage
pattern CaseReduceStage = Left CaseReduce

pattern InlineStage :: OptStage
pattern InlineStage = Right Inline

pattern CseStage :: OptStage
pattern CseStage = Right CSE

pattern ApplyToCaseStage :: OptStage
pattern ApplyToCaseStage = Right ApplyToCase

pattern CaseOfCaseStage :: OptStage
pattern CaseOfCaseStage = Left CaseOfCase

pattern LetFloatOutStage :: OptStage
pattern LetFloatOutStage = Left LetFloatOut

{-# COMPLETE
  FloatDelayStage
  , ForceDelayStage
  , ForceCaseDelayStage
  , CaseReduceStage
  , InlineStage
  , CseStage
  , ApplyToCaseStage
  , CaseOfCaseStage
  , LetFloatOutStage
  #-}

data Optimization name uni fun a
  = Optimization
  { beforeAST :: Term name uni fun a
  , stage :: OptStage
  , hints :: Certify.Hints
  , afterAST :: Term name uni fun a
  }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype OptimizerTrace name uni fun a
  = OptimizerTrace
  { optimizerTrace
      :: [Optimization name uni fun a]
  }

initOptimizerTrace :: OptimizerTrace name uni fun a
initOptimizerTrace = OptimizerTrace []

allASTs :: OptimizerTrace name uni fun a -> [Term name uni fun a]
allASTs = \case
  OptimizerTrace [] -> []
  OptimizerTrace xs@(x : _) ->
    -- `OptimizerTrace` is in reverse order: the first item is the last pass run.
    afterAST x : map beforeAST xs
