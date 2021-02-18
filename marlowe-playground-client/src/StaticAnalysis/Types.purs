module StaticAnalysis.Types where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Marlowe.Extended (TemplateContent)
import Marlowe.Semantics (AccountId, Case, Contract, Observation, Payee, Timeout, Token, Value, ValueId)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result)
import Network.RemoteData (isLoading)
import Types (WarningAnalysisData)

-------------------------------------------------------------------------------
type AnalysisState
  = { templateContent :: TemplateContent
    , analysisExecutionState :: AnalysisExecutionState
    }

_templateContent :: forall s a. Lens' { templateContent :: a | s } a
_templateContent = prop (SProxy :: SProxy "templateContent")

_analysisExecutionState :: forall s a. Lens' { analysisExecutionState :: a | s } a
_analysisExecutionState = prop (SProxy :: SProxy "analysisExecutionState")

initAnalysisState :: AnalysisState
initAnalysisState =
  { templateContent: mempty
  , analysisExecutionState: NoneAsked
  }

data AnalysisExecutionState
  = NoneAsked
  | WarningAnalysis (WarningAnalysisData Result)
  | ReachabilityAnalysis MultiStageAnalysisData
  | CloseAnalysis MultiStageAnalysisData

_analysisState :: forall s. Lens' { analysisState :: AnalysisState | s } AnalysisState
_analysisState = prop (SProxy :: SProxy "analysisState")

isStaticLoading :: AnalysisExecutionState -> Boolean
isStaticLoading (WarningAnalysis remoteData) = isLoading remoteData

isStaticLoading _ = false

isReachabilityLoading :: AnalysisExecutionState -> Boolean
isReachabilityLoading (ReachabilityAnalysis (AnalysisInProgress _)) = true

isReachabilityLoading (ReachabilityAnalysis AnalysisNotStarted) = true

isReachabilityLoading _ = false

isCloseAnalysisLoading :: AnalysisExecutionState -> Boolean
isCloseAnalysisLoading (CloseAnalysis (AnalysisInProgress _)) = true

isCloseAnalysisLoading (CloseAnalysis AnalysisNotStarted) = true

isCloseAnalysisLoading _ = false

isNoneAsked :: AnalysisExecutionState -> Boolean
isNoneAsked NoneAsked = true

isNoneAsked _ = false

-------------------------------------------------------------------------------
data MultiStageAnalysisData
  = AnalysisNotStarted
  | AnalysisInProgress AnalysisInProgressRecord
  | AnalysisFailure String
  | AnalysisFoundCounterExamples AnalysisCounterExamplesRecord
  | AnalysisFinishedAndPassed

type AnalysisCounterExamplesRecord
  = { originalState :: S.State
    , originalContract :: Contract
    , counterExampleSubcontracts :: NonEmptyList ContractPath
    }

type AnalysisInProgressRecord
  = { currPath :: ContractPath
    , currContract :: Contract
    , currChildren :: RemainingSubProblemInfo
    , originalState :: S.State
    , originalContract :: Contract
    , subproblems :: RemainingSubProblemInfo
    , numSubproblems :: Int
    , numSolvedSubproblems :: Int
    , counterExampleSubcontracts :: List ContractPath
    }

-------------------------------------------------------------------------------
type ContractPath
  = List ContractPathStep

data ContractPathStep
  = PayContPath
  | IfTruePath
  | IfFalsePath
  | WhenCasePath Int
  | WhenTimeoutPath
  | LetPath
  | AssertPath

derive instance eqContractPathStep :: Eq ContractPathStep

derive instance ordContractPathStep :: Ord ContractPathStep

derive instance genericContractPathStep :: Generic ContractPathStep _

instance showContractPathStep :: Show ContractPathStep where
  show = genericShow

type RemainingSubProblemInfo
  = List (ContractZipper /\ Contract)

data ContractZipper
  = PayZip AccountId Payee Token Value ContractZipper
  | IfTrueZip Observation ContractZipper Contract
  | IfFalseZip Observation Contract ContractZipper
  | WhenCaseZip (List Case) S.Action ContractZipper (List Case) Timeout Contract -- First list is stored reversed for efficiency
  | WhenTimeoutZip (Array Case) Timeout ContractZipper
  | LetZip ValueId Value ContractZipper
  | AssertZip Observation ContractZipper
  | HeadZip

type MultiStageAnalysisProblemDef
  = { expandSubproblemImpl :: ContractZipper -> Contract -> (ContractPath /\ Contract)
    , isValidSubproblemImpl :: ContractZipper -> Contract -> Boolean
    , analysisDataSetter :: MultiStageAnalysisData -> AnalysisExecutionState
    , shouldExamineChildren :: Boolean -> Boolean
    , isProblemCounterExample :: Boolean -> Boolean
    }

type PrefixMap
  = Map ContractPathStep (Set (NonEmptyList ContractPathStep))
