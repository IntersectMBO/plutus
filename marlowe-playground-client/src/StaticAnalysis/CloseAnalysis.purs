module CloseAnalysis where

-- FIXME: run import clean before merging.
import Prelude hiding (div)
import Control.Monad.Except (lift)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (runMaybeT)
import Data.Either (hush)
import Data.Foldable (foldl)
import Data.Lens (assign)
import Data.List (List(..))
import Data.List.NonEmpty (toList)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Marlowe.Holes (fromTerm)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Contract(..), Observation(..), Payee(..), Token, Value(..), emptyState)
import Marlowe.Semantics as S
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.StaticTools (closeZipperContract, startMultiStageAnalysis, zipperToContractPath)
import StaticAnalysis.Types (AnalysisState(..), ContractPath, ContractZipper(..), MultiStageAnalysisData(..), MultiStageAnalysisProblemDef, _analysisState)

analyseClose ::
  forall m state action slots.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  String ->
  HalogenM { analysisState :: AnalysisState | state } action slots Void m Unit
analyseClose settings contents =
  void
    $ runMaybeT do
        contract <- hoistMaybe $ parseContract' contents
        assign _analysisState (CloseAnalysis AnalysisNotStarted)
        -- when editor and simulator were together the analyse contract could be made
        -- at any step of the simulator. Now that they are separate, it can only be done
        -- with initial state
        let
          emptySemanticState = emptyState zero
        newCloseAnalysisState <- lift $ startCloseAnalysis settings contract emptySemanticState
        assign _analysisState (CloseAnalysis newCloseAnalysisState)
  where
  parseContract' = fromTerm <=< hush <<< parseContract

extractAccountIdsFromZipper :: ContractZipper -> Set (AccountId /\ Token)
extractAccountIdsFromZipper = go
  where
  go (PayZip _ (Account accountId) token _ contZip) = Set.insert (accountId /\ token) $ go contZip

  go (PayZip _ _ _ _ contZip) = go contZip

  go (WhenCaseZip _ (S.Deposit accountId _ token _) contZip _ _ _) = Set.insert (accountId /\ token) $ go contZip

  go (WhenCaseZip _ _ contZip _ _ _) = go contZip

  go (IfTrueZip _ contZip _) = go contZip

  go (IfFalseZip _ _ contZip) = go contZip

  go (WhenTimeoutZip _ _ contZip) = go contZip

  go (LetZip _ _ contZip) = go contZip

  go (AssertZip _ contZip) = go contZip

  go HeadZip = mempty

addAssertionForAccountId :: Contract -> (AccountId /\ Token) -> Contract
addAssertionForAccountId cont (accountId /\ token) = Assert (ValueEQ (AvailableMoney accountId token) (Constant zero)) cont

-- We expect "contract" to be Close always, but we take it as a parameter anyway because it makes more sense
expandSubproblem :: ContractZipper -> Contract -> (ContractPath /\ Contract)
expandSubproblem zipper contract = zipperToContractPath zipper /\ closeZipperContract zipper modifiedContract
  where
  accountIds = extractAccountIdsFromZipper zipper

  modifiedContract = foldl addAssertionForAccountId contract accountIds

isValidSubproblem :: ContractZipper -> Contract -> Boolean
isValidSubproblem _ Close = true

isValidSubproblem _ _ = false

closeAnalysisAnalysisDef :: MultiStageAnalysisProblemDef
closeAnalysisAnalysisDef =
  { analysisDataSetter: CloseAnalysis
  , expandSubproblemImpl: expandSubproblem
  , isValidSubproblemImpl: isValidSubproblem
  , shouldExamineChildren: const true
  , isProblemCounterExample: not
  }

startCloseAnalysis ::
  forall m state action slots.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State -> HalogenM { analysisState :: AnalysisState | state } action slots Void m MultiStageAnalysisData
startCloseAnalysis = startMultiStageAnalysis closeAnalysisAnalysisDef
