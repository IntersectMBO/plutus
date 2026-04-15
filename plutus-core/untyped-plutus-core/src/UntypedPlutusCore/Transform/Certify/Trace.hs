{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module UntypedPlutusCore.Transform.Certify.Trace where

import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify

import Control.DeepSeq
import GHC.Generics

{-| Datatype which represents optimization passes which are also
certified (__I__mplemented in the __C__ertifier).

This means that these passes are formalized as part of the certifier,
and adding a new pass constructor to this type means that it is expected
the pass will be also certified in the same PR. -}
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

{-| Datatype which represents optimization passes which are not yet
certified (__N__ot __I__mplemented in the __C__ertifier).

IMPORTANT: if you add a new pass, or modify an existing pass, without
also modifying the certifier in the same PR, you must add/move its
corresponding constructor to this type. Please also open an issue
at https://github.com/IntersectMBO/plutus/issues. -}
data NICSimplifierStage
  = CaseOfCase
  | LetFloatOut
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

type SimplifierStage = Either NICSimplifierStage ICSimplifierStage

pattern FloatDelayStage :: SimplifierStage
pattern FloatDelayStage = Right FloatDelay

pattern ForceDelayStage :: SimplifierStage
pattern ForceDelayStage = Right ForceDelay

pattern ForceCaseDelayStage :: SimplifierStage
pattern ForceCaseDelayStage = Right ForceCaseDelay

pattern CaseReduceStage :: SimplifierStage
pattern CaseReduceStage = Right CaseReduce

pattern InlineStage :: SimplifierStage
pattern InlineStage = Right Inline

pattern CseStage :: SimplifierStage
pattern CseStage = Right CSE

pattern ApplyToCaseStage :: SimplifierStage
pattern ApplyToCaseStage = Right ApplyToCase

pattern CaseOfCaseStage :: SimplifierStage
pattern CaseOfCaseStage = Left CaseOfCase

pattern LetFloatOutStage :: SimplifierStage
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
