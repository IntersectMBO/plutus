module StaticAnalysis.Reachability (areContractAndStateTheOnesAnalysed, getUnreachableContracts, initialisePrefixMap, startReachabilityAnalysis, stepPrefixMap, updateWithResponse) where

import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State as CMS
import Data.Foldable (for_)
import Data.Function (flip, identity)
import Data.Lens (assign)
import Data.List (List(..), any, catMaybes, fromFoldable, length, null)
import Data.List.NonEmpty (NonEmptyList(..), fromList, head, tail, toList)
import Data.Map (fromFoldableWith, lookup, unionWith)
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Set (singleton, union)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, query)
import Halogen.Monaco as Monaco
import MainFrame.Types (ChildSlots, _marloweEditorSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Semantics (Contract(..), Observation(..))
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Request as MSReq
import Marlowe.Symbolic.Types.Response (Result(..))
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, discard, map, mempty, pure, unit, void, when, ($), (&&), (+), (-), (/=), (<$>), (<>), (==), (>))
import Servant.PureScript.Ajax (AjaxError(..))
import Servant.PureScript.Settings (SPSettings_)
import Simulation.Types (Action, AnalysisState(..), ContractPath, ContractPathStep, ContractZipper(..), AnalysisInProgressRecord, PrefixMap, MultiStageAnalysisData(..), State, WebData, _analysisState)
import StaticAnalysis.StaticTools (closeZipperContract, countSubproblems, getNextSubproblem, initSubproblems, zipperToContractPath)

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

checkContractForReachability ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State ->
  HalogenM State Action ChildSlots Void m (WebData Result)
checkContractForReachability settings contract state = runAjax $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract: contract, state: state }))

expandSubproblem :: ContractZipper -> (ContractPath /\ Contract)
expandSubproblem z = zipperToContractPath z /\ closeZipperContract z (Assert FalseObs Close)

isValidSubproblem :: ContractZipper -> Contract -> Boolean
isValidSubproblem (IfTrueZip _ _ _) c
  | c /= Close = true

isValidSubproblem (IfFalseZip _ _ _) c
  | c /= Close = true

isValidSubproblem (WhenCaseZip _ _ _ _ _ _) c
  | c /= Close = true

isValidSubproblem _ _ = false

startReachabilityAnalysis ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State -> HalogenM State Action ChildSlots Void m MultiStageAnalysisData
startReachabilityAnalysis settings contract state = do
  case getNextSubproblem isValidSubproblem initialSubproblems Nil of
    Nothing -> pure AnalysisFinishedAndPassed
    Just ((contractZipper /\ _ /\ newChildren) /\ newSubproblems) -> do
      let
        numSubproblems = countSubproblems isValidSubproblem (newChildren <> newSubproblems)

        newPath /\ newContract = expandSubproblem contractZipper

        progress =
          ( AnalysisInProgress
              { currPath: newPath
              , currContract: newContract
              , currChildren: newChildren
              , originalState: state
              , originalContract: contract
              , subproblems: newSubproblems
              , numSubproblems: 1 + numSubproblems
              , numSolvedSubproblems: 0
              , counterExampleSubcontracts: Nil
              }
          )
      assign _analysisState (ReachabilityAnalysis progress)
      response <- checkContractForReachability settings newContract state
      result <- updateWithResponse settings progress response
      pure result
  where
  initialSubproblems = initSubproblems contract

stepSubproblem :: Boolean -> AnalysisInProgressRecord -> Boolean /\ AnalysisInProgressRecord
stepSubproblem isReachable ( rad@{ currPath: oldPath
  , originalState: state
  , subproblems: oldSubproblems
  , currChildren: oldChildren
  , numSolvedSubproblems: n
  , numSubproblems: oldTotalN
  , counterExampleSubcontracts: results
  }
) = case getNextSubproblem isValidSubproblem oldSubproblems (if isReachable then oldChildren else Nil) of
  Just ((contractZipper /\ subcontract /\ newChildren) /\ newSubproblems) ->
    let
      newPath /\ newContract = expandSubproblem contractZipper
    in
      true
        /\ ( rad
              { currPath = newPath
              , currContract = newContract
              , currChildren = newChildren
              , subproblems = newSubproblems
              , numSolvedSubproblems = newN
              , numSubproblems = newTotalN
              , counterExampleSubcontracts = newResults
              }
          )
  Nothing ->
    false
      /\ ( rad
            { subproblems = Nil
            , numSolvedSubproblems = newN
            , numSubproblems = newTotalN
            , counterExampleSubcontracts = newResults
            }
        )
  where
  newN = n + 1

  newTotalN = oldTotalN - (if isReachable then 0 else countSubproblems isValidSubproblem oldChildren)

  newResults = results <> (if isReachable then Nil else Cons oldPath Nil)

finishAnalysis :: AnalysisInProgressRecord -> MultiStageAnalysisData
finishAnalysis { originalState, originalContract, counterExampleSubcontracts: Cons h t } = AnalysisFoundCounterExamples { originalState, originalContract, counterExampleSubcontracts: NonEmptyList (h :| t) }

finishAnalysis { counterExampleSubcontracts: Nil } = AnalysisFinishedAndPassed

stepAnalysis :: forall m. MonadAff m => SPSettings_ SPParams_ -> Boolean -> AnalysisInProgressRecord -> HalogenM State Action ChildSlots Void m MultiStageAnalysisData
stepAnalysis settings isReachable rad =
  let
    thereAreMore /\ newRad = stepSubproblem isReachable rad

    thereAreNewCounterExamples = length newRad.counterExampleSubcontracts > length rad.counterExampleSubcontracts
  in
    if thereAreMore then do
      assign _analysisState (ReachabilityAnalysis (AnalysisInProgress newRad))
      when thereAreNewCounterExamples refreshEditor
      response <- checkContractForReachability settings (newRad.currContract) (newRad.originalState)
      updateWithResponse settings (AnalysisInProgress newRad) response
    else do
      let
        result = finishAnalysis newRad
      assign _analysisState (ReachabilityAnalysis result)
      when thereAreNewCounterExamples refreshEditor
      pure result
  where
  refreshEditor = do
    mContent <- query _marloweEditorSlot unit (Monaco.GetText identity)
    for_ mContent (\content -> void $ query _marloweEditorSlot unit $ Monaco.SetText content unit)

updateWithResponse ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  MultiStageAnalysisData ->
  WebData Result -> HalogenM State Action ChildSlots Void m MultiStageAnalysisData
updateWithResponse _ (AnalysisInProgress _) (Failure (AjaxError err)) = pure (AnalyisisFailure "connection error")

updateWithResponse _ (AnalysisInProgress { currPath: path }) (Success (Error err)) = pure (AnalyisisFailure err)

updateWithResponse settings (AnalysisInProgress rad) (Success Valid) = stepAnalysis settings false rad

updateWithResponse settings (AnalysisInProgress rad) (Success (CounterExample _)) = stepAnalysis settings true rad

updateWithResponse _ rad _ = pure rad

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
