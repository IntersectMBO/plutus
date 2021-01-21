module CloseAnalysis where

import Data.Foldable (foldl)
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
import Marlowe.Semantics (AccountId, Contract(..), Observation(..), Payee(..), Token, Value(..))
import Marlowe.Semantics as S
import MarloweEditor.Types (Action, AnalysisState(..), ContractPath, ContractZipper(..), MultiStageAnalysisData(..), MultiStageAnalysisProblemDef, State)
import Prelude (Void, const, mempty, not, zero, ($), (&&), (==))
import Servant.PureScript.Settings (SPSettings_)
import StaticAnalysis.StaticTools (closeZipperContract, startMultiStageAnalysis, zipperToContractPath)

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
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Contract ->
  S.State -> HalogenM State Action ChildSlots Void m MultiStageAnalysisData
startCloseAnalysis = startMultiStageAnalysis closeAnalysisAnalysisDef
