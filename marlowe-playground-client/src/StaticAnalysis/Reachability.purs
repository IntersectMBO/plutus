module StaticAnalysis.Reachability
  ( analyseReachability
  , areContractAndStateTheOnesAnalysed
  , getUnreachableContracts
  , initialisePrefixMap
  , startReachabilityAnalysis
  , stepPrefixMap
  ) where

import Prelude hiding (div)
import Control.Monad.State as CMS
import Control.Monad.Reader (class MonadAsk)
import Data.Lens (assign)
import Data.List (List(..), any, catMaybes, fromFoldable, null)
import Data.List.NonEmpty (fromList, head, tail, toList)
import Data.Map (fromFoldableWith, lookup, unionWith)
import Data.Maybe (Maybe(..))
import Data.Set (singleton, union)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM)
import Marlowe.Semantics (Contract(..), Observation(..), emptyState)
import Marlowe.Semantics as S
import Marlowe.Extended (toCore)
import Marlowe.Extended as EM
import StaticAnalysis.StaticTools (closeZipperContract, startMultiStageAnalysis, zipperToContractPath)
import StaticAnalysis.Types (AnalysisState(..), ContractPath, ContractPathStep, ContractZipper(..), MultiStageAnalysisData(..), MultiStageAnalysisProblemDef, PrefixMap, _analysisState)

analyseReachability ::
  forall m state action slots.
  MonadAff m =>
  MonadAsk Env m =>
  EM.Contract ->
  HalogenM { analysisState :: AnalysisState | state } action slots Void m Unit
analyseReachability extendedContract = do
  case toCore extendedContract of
    Just contract -> do
      assign _analysisState (ReachabilityAnalysis AnalysisNotStarted)
      -- when editor and simulator were together the analyse contract could be made
      -- at any step of the simulator. Now that they are separate, it can only be done
      -- with initial state
      let
        emptySemanticState = emptyState zero
      newReachabilityAnalysisState <- startReachabilityAnalysis contract emptySemanticState
      assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)
    Nothing -> assign _analysisState (ReachabilityAnalysis $ AnalysisFailure "The code has templates. Static analysis can only be run in core Marlowe code.")

expandSubproblem :: ContractZipper -> Contract -> (ContractPath /\ Contract)
expandSubproblem z _ = zipperToContractPath z /\ closeZipperContract z (Assert FalseObs Close)

isValidSubproblem :: ContractZipper -> Contract -> Boolean
isValidSubproblem (IfTrueZip _ _ _) c
  | c /= Close = true

isValidSubproblem (IfFalseZip _ _ _) c
  | c /= Close = true

isValidSubproblem (WhenCaseZip _ _ _ _ _ _) c
  | c /= Close = true

isValidSubproblem _ _ = false

reachabilityAnalysisDef :: MultiStageAnalysisProblemDef
reachabilityAnalysisDef =
  { analysisDataSetter: ReachabilityAnalysis
  , expandSubproblemImpl: expandSubproblem
  , isValidSubproblemImpl: isValidSubproblem
  , shouldExamineChildren: identity
  , isProblemCounterExample: identity
  }

startReachabilityAnalysis ::
  forall m state action slots.
  MonadAff m =>
  MonadAsk Env m =>
  Contract ->
  S.State -> HalogenM { analysisState :: AnalysisState | state } action slots Void m MultiStageAnalysisData
startReachabilityAnalysis = startMultiStageAnalysis reachabilityAnalysisDef

getUnreachableContracts :: AnalysisState -> List ContractPath
getUnreachableContracts (ReachabilityAnalysis (AnalysisInProgress ipr)) = ipr.counterExampleSubcontracts

getUnreachableContracts (ReachabilityAnalysis (AnalysisFoundCounterExamples us)) = toList us.counterExampleSubcontracts

getUnreachableContracts _ = Nil

areContractAndStateTheOnesAnalysed :: AnalysisState -> Maybe Contract -> S.State -> Boolean
areContractAndStateTheOnesAnalysed (ReachabilityAnalysis (AnalysisInProgress ipr)) (Just contract) state = ipr.originalContract == contract && ipr.originalState == state

areContractAndStateTheOnesAnalysed (ReachabilityAnalysis (AnalysisFoundCounterExamples us)) (Just contract) state = us.originalContract == contract && us.originalState == state

areContractAndStateTheOnesAnalysed _ _ _ = false

-- It groups the contract paths by their head, discards empty contract paths
initialisePrefixMap :: List ContractPath -> PrefixMap
initialisePrefixMap unreachablePathList = fromFoldableWith union $ map (\x -> (head x /\ singleton x)) $ catMaybes $ map fromList unreachablePathList

-- Returns Nothing when the path is unreachable according to one of the paths, otherwise it returns the updated PrefixMap for the subpath
stepPrefixMap :: forall a. CMS.State a Unit -> PrefixMap -> ContractPathStep -> CMS.State a (Maybe PrefixMap)
stepPrefixMap markUnreachable prefixMap contractPath = case lookup contractPath prefixMap of
  Just pathSet ->
    let
      tails = map tail $ fromFoldable pathSet
    in
      if any null tails then do
        markUnreachable
        pure Nothing
      else
        pure $ Just $ unionWith union (initialisePrefixMap tails) mempty
  Nothing -> pure (Just mempty)
