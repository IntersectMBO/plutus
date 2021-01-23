module StaticAnalysis.Reachability (areContractAndStateTheOnesAnalysed, getUnreachableContracts, initialisePrefixMap, startReachabilityAnalysis, stepPrefixMap) where

import Prelude hiding (div)
import Control.Monad.State as CMS
import Data.List (List(..), any, catMaybes, fromFoldable, null)
import Data.List.NonEmpty (fromList, head, tail, toList)
import Data.Map (fromFoldableWith, lookup, unionWith)
import Data.Maybe (Maybe(..))
import Data.Set (singleton, union)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Marlowe.Semantics (Contract(..), Observation(..))
import Marlowe.Semantics as S
import MarloweEditor.Types (Action, AnalysisState(..), ContractPath, ContractPathStep, ContractZipper(..), MultiStageAnalysisData(..), MultiStageAnalysisProblemDef, PrefixMap, State)
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.StaticTools (closeZipperContract, startMultiStageAnalysis, zipperToContractPath)

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
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State -> HalogenM State Action ChildSlots Void m MultiStageAnalysisData
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
