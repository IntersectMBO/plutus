module Reachability (areContractAndStateTheOnesAnalysed, getUnreachableContracts, initialisePrefixMap, startReachabilityAnalysis, stepPrefixMap, updateWithResponse) where

import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State as CMS
import Data.Foldable (for_)
import Data.Function (flip, identity)
import Data.Lens (assign)
import Data.List (List(..), any, catMaybes, foldl, fromFoldable, length, null, snoc, toUnfoldable)
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
import Marlowe.Semantics (Case(..), Contract(..), Observation(..))
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Request as MSReq
import Marlowe.Symbolic.Types.Response (Result(..))
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, discard, map, mempty, pure, unit, void, when, ($), (&&), (+), (-), (/=), (<$>), (<>), (==), (>))
import Servant.PureScript.Ajax (AjaxError(..))
import Servant.PureScript.Settings (SPSettings_)
import Simulation.Types (Action, AnalysisState(..), ContractPath, ContractPathStep(..), ContractZipper(..), InProgressRecord, ReachabilityAnalysisData(..), RemainingSubProblemInfo, State, WebData, PrefixMap, _analysisState)

splitArray :: forall a. List a -> List (List a /\ a /\ List a)
splitArray x = splitArrayAux Nil x

splitArrayAux :: forall a. List a -> List a -> List (List a /\ a /\ List a)
splitArrayAux _ Nil = Nil

splitArrayAux l (Cons h t) = Cons (l /\ h /\ t) (splitArrayAux (Cons h l) t)

expandChildren :: ContractZipper -> Contract -> RemainingSubProblemInfo
expandChildren _ Close = Nil

expandChildren zipper (Pay accId payee tok val cont) = Cons (PayZip accId payee tok val zipper /\ cont) Nil

expandChildren zipper (If obs cont1 cont2) = Cons (IfTrueZip obs zipper cont2 /\ cont1) (Cons (IfFalseZip obs cont1 zipper /\ cont2) Nil)

expandChildren zipper (When cases tim tcont) =
  snoc
    ( map (\(before /\ Case act cont /\ after) -> WhenCaseZip before act zipper after tim tcont /\ cont)
        (splitArray (fromFoldable cases))
    )
    (WhenTimeoutZip cases tim zipper /\ tcont)

expandChildren zipper (Let valId val cont) = Cons (LetZip valId val zipper /\ cont) Nil

expandChildren zipper (Assert obs cont) = Cons (AssertZip obs zipper /\ cont) Nil

closeZipperContract :: ContractZipper -> Contract -> Contract
closeZipperContract (PayZip accId payee tok val zipper) cont = closeZipperContract zipper (Pay accId payee tok val cont)

closeZipperContract (IfTrueZip obs zipper cont2) cont1 = closeZipperContract zipper (If obs cont1 cont2)

closeZipperContract (IfFalseZip obs cont1 zipper) cont2 = closeZipperContract zipper (If obs cont1 cont2)

closeZipperContract (WhenCaseZip bef act zipper aft tim timcont) cont =
  let
    thisCase = Case act cont

    cases = toUnfoldable (foldl (flip Cons) (Cons thisCase aft) bef)
  in
    closeZipperContract zipper (When cases tim timcont)

closeZipperContract (WhenTimeoutZip cases tim zipper) timcont = closeZipperContract zipper (When cases tim timcont)

closeZipperContract (LetZip valId val zipper) cont = closeZipperContract zipper (Let valId val cont)

closeZipperContract (AssertZip obs zipper) cont = closeZipperContract zipper (Assert obs cont)

closeZipperContract HeadZip cont = cont

zipperToContractPathAux :: ContractZipper -> ContractPath -> ContractPath
zipperToContractPathAux (PayZip _ _ _ _ zipper) p = zipperToContractPathAux zipper (Cons PayContPath p)

zipperToContractPathAux (IfTrueZip _ zipper _) p = zipperToContractPathAux zipper (Cons IfTruePath p)

zipperToContractPathAux (IfFalseZip _ _ zipper) p = zipperToContractPathAux zipper (Cons IfFalsePath p)

zipperToContractPathAux (WhenCaseZip bef _ zipper _ _ _) p = zipperToContractPathAux zipper (Cons (WhenCasePath (length bef)) p)

zipperToContractPathAux (WhenTimeoutZip _ _ zipper) p = zipperToContractPathAux zipper (Cons WhenTimeoutPath p)

zipperToContractPathAux (LetZip _ _ zipper) p = zipperToContractPathAux zipper (Cons LetPath p)

zipperToContractPathAux (AssertZip _ zipper) p = zipperToContractPathAux zipper (Cons AssertPath p)

zipperToContractPathAux HeadZip p = p

zipperToContractPath :: ContractZipper -> ContractPath
zipperToContractPath zipper = zipperToContractPathAux zipper Nil

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

nullifyAsserts :: Contract -> Contract
nullifyAsserts Close = Close

nullifyAsserts (Pay accId payee tok val cont) = Pay accId payee tok val (nullifyAsserts cont)

nullifyAsserts (If obs cont1 cont2) = If obs (nullifyAsserts cont1) (nullifyAsserts cont2)

nullifyAsserts (When cases timeout timCont) =
  When
    ( do
        Case act cont <- cases
        pure (Case act (nullifyAsserts cont))
    )
    timeout
    (nullifyAsserts timCont)

nullifyAsserts (Let valId val cont) = Let valId val (nullifyAsserts cont)

nullifyAsserts (Assert obs cont) = Assert TrueObs cont

startReachabilityAnalysis ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State -> HalogenM State Action ChildSlots Void m ReachabilityAnalysisData
startReachabilityAnalysis settings contract state = do
  case getNextSubproblem isValidSubproblem initialSubproblems Nil of
    Nothing -> pure AllReachable
    Just ((contractZipper /\ _ /\ newChildren) /\ newSubproblems) -> do
      let
        numSubproblems = countSubproblems isValidSubproblem (newChildren <> newSubproblems)

        newPath /\ newContract = expandSubproblem contractZipper

        progress =
          ( InProgress
              { currPath: newPath
              , currContract: newContract
              , currChildren: newChildren
              , originalState: state
              , originalContract: contract
              , subproblems: newSubproblems
              , numSubproblems: 1 + numSubproblems
              , numSolvedSubproblems: 0
              , unreachableSubcontracts: Nil
              }
          )
      assign _analysisState (ReachabilityAnalysis progress)
      response <- checkContractForReachability settings newContract state
      result <- updateWithResponse settings progress response
      pure result
  where
  initialSubproblems = initSubproblems contract

initSubproblems :: Contract -> RemainingSubProblemInfo
initSubproblems c = Cons (HeadZip /\ c) Nil

countFix :: forall a. (a -> Maybe a) -> a -> Int
countFix fun a0 = countFix_tailrec fun a0 0
  where
  countFix_tailrec :: (a -> Maybe a) -> a -> Int -> Int
  countFix_tailrec f a acc = case f a of
    Nothing -> acc
    Just newA -> countFix_tailrec f newA (acc + 1)

countSubproblems :: (ContractZipper -> Contract -> Boolean) -> RemainingSubProblemInfo -> Int
countSubproblems _ Nil = 0

countSubproblems filterFun subproblemInfo = countFix fixpointFun (Nil /\ subproblemInfo)
  where
  fixpointFun :: (RemainingSubProblemInfo /\ RemainingSubProblemInfo) -> Maybe (RemainingSubProblemInfo /\ RemainingSubProblemInfo)
  fixpointFun (children /\ subproblems) = map (\((_ /\ _ /\ c) /\ a) -> (c /\ a)) $ getNextSubproblem filterFun subproblems children

getNextSubproblem ::
  (ContractZipper -> Contract -> Boolean) ->
  RemainingSubProblemInfo ->
  RemainingSubProblemInfo ->
  Maybe ((ContractZipper /\ Contract /\ RemainingSubProblemInfo) /\ RemainingSubProblemInfo)
getNextSubproblem _ Nil Nil = Nothing

getNextSubproblem f (Cons (zipper /\ contract) rest) Nil =
  if f zipper contract then
    Just ((zipper /\ contract /\ children) /\ rest)
  else
    getNextSubproblem f rest children
  where
  children = expandChildren zipper contract

getNextSubproblem f acc newChildren = getNextSubproblem f (acc <> newChildren) Nil

stepSubproblem :: Boolean -> InProgressRecord -> Boolean /\ InProgressRecord
stepSubproblem isReachable ( rad@{ currPath: oldPath
  , originalState: state
  , subproblems: oldSubproblems
  , currChildren: oldChildren
  , numSolvedSubproblems: n
  , numSubproblems: oldTotalN
  , unreachableSubcontracts: results
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
              , unreachableSubcontracts = newResults
              }
          )
  Nothing ->
    false
      /\ ( rad
            { subproblems = Nil
            , numSolvedSubproblems = newN
            , numSubproblems = newTotalN
            , unreachableSubcontracts = newResults
            }
        )
  where
  newN = n + 1

  newTotalN = oldTotalN - (if isReachable then 0 else countSubproblems isValidSubproblem oldChildren)

  newResults = results <> (if isReachable then Nil else Cons oldPath Nil)

finishAnalysis :: InProgressRecord -> ReachabilityAnalysisData
finishAnalysis { originalState, originalContract, unreachableSubcontracts: Cons h t } = UnreachableSubcontract { originalState, originalContract, unreachableSubcontracts: NonEmptyList (h :| t) }

finishAnalysis { unreachableSubcontracts: Nil } = AllReachable

stepAnalysis :: forall m. MonadAff m => SPSettings_ SPParams_ -> Boolean -> InProgressRecord -> HalogenM State Action ChildSlots Void m ReachabilityAnalysisData
stepAnalysis settings isReachable rad =
  let
    thereAreMore /\ newRad = stepSubproblem isReachable rad

    thereAreNewCounterExamples = length newRad.unreachableSubcontracts > length rad.unreachableSubcontracts
  in
    if thereAreMore then do
      assign _analysisState (ReachabilityAnalysis (InProgress newRad))
      when thereAreNewCounterExamples refreshEditor
      response <- checkContractForReachability settings (newRad.currContract) (newRad.originalState)
      updateWithResponse settings (InProgress newRad) response
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
  ReachabilityAnalysisData ->
  WebData Result -> HalogenM State Action ChildSlots Void m ReachabilityAnalysisData
updateWithResponse _ (InProgress _) (Failure (AjaxError err)) = pure (ReachabilityFailure "connection error")

updateWithResponse _ (InProgress { currPath: path }) (Success (Error err)) = pure (ReachabilityFailure err)

updateWithResponse settings (InProgress rad) (Success Valid) = stepAnalysis settings false rad

updateWithResponse settings (InProgress rad) (Success (CounterExample _)) = stepAnalysis settings true rad

updateWithResponse _ rad _ = pure rad

getUnreachableContracts :: AnalysisState -> List ContractPath
getUnreachableContracts (ReachabilityAnalysis (InProgress ipr)) = ipr.unreachableSubcontracts

getUnreachableContracts (ReachabilityAnalysis (UnreachableSubcontract us)) = toList us.unreachableSubcontracts

getUnreachableContracts _ = Nil

areContractAndStateTheOnesAnalysed :: AnalysisState -> Maybe Contract -> S.State -> Boolean
areContractAndStateTheOnesAnalysed (ReachabilityAnalysis (InProgress ipr)) (Just contract) state = ipr.originalContract == contract && ipr.originalState == state

areContractAndStateTheOnesAnalysed (ReachabilityAnalysis (UnreachableSubcontract us)) (Just contract) state = us.originalContract == contract && us.originalState == state

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
