{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V2.EvaluationContext
    ( module V1.EvaluationContext
    , mkEvaluationContext
    , costModelParamNames
    , ParamName -- abstract
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1.EvaluationContext as V1.EvaluationContext hiding (ParamName, costModelParamNames,
                                                                     mkEvaluationContext)

import Control.Monad
import Control.Monad.Except
import Data.Ix
import Data.List.Extra
import Data.Text qualified as Text
import GHC.Generics

-- | The set of valid names that a cost model parameter can take for this language version.
-- It is used for the deserialization of `CostModelParams` and their order in the list is fixed.
costModelParamNames :: [Text.Text]
costModelParamNames = Text.pack . showParamName <$> enumerate @ParamName

{-| The enumeration of all possible cost model parameter names for this language version.
IMPORTANT: The order of appearance of the data constructors here matters. DO NOT REORDER.
See Note [Quotation marks in cost model parameter constructors]
-}
data ParamName =
    AddInteger'cpu'arguments'intercept
  | AddInteger'cpu'arguments'slope
  | AddInteger'memory'arguments'intercept
  | AddInteger'memory'arguments'slope
  | AppendByteString'cpu'arguments'intercept
  | AppendByteString'cpu'arguments'slope
  | AppendByteString'memory'arguments'intercept
  | AppendByteString'memory'arguments'slope
  | AppendString'cpu'arguments'intercept
  | AppendString'cpu'arguments'slope
  | AppendString'memory'arguments'intercept
  | AppendString'memory'arguments'slope
  | BData'cpu'arguments
  | BData'memory'arguments
  | Blake2b_256'cpu'arguments'intercept
  | Blake2b_256'cpu'arguments'slope
  | Blake2b_256'memory'arguments
  | CekApplyCost'exBudgetCPU
  | CekApplyCost'exBudgetMemory
  | CekBuiltinCost'exBudgetCPU
  | CekBuiltinCost'exBudgetMemory
  | CekConstCost'exBudgetCPU
  | CekConstCost'exBudgetMemory
  | CekDelayCost'exBudgetCPU
  | CekDelayCost'exBudgetMemory
  | CekForceCost'exBudgetCPU
  | CekForceCost'exBudgetMemory
  | CekLamCost'exBudgetCPU
  | CekLamCost'exBudgetMemory
  | CekStartupCost'exBudgetCPU
  | CekStartupCost'exBudgetMemory
  | CekVarCost'exBudgetCPU
  | CekVarCost'exBudgetMemory
  | ChooseData'cpu'arguments
  | ChooseData'memory'arguments
  | ChooseList'cpu'arguments
  | ChooseList'memory'arguments
  | ChooseUnit'cpu'arguments
  | ChooseUnit'memory'arguments
  | ConsByteString'cpu'arguments'intercept
  | ConsByteString'cpu'arguments'slope
  | ConsByteString'memory'arguments'intercept
  | ConsByteString'memory'arguments'slope
  | ConstrData'cpu'arguments
  | ConstrData'memory'arguments
  | DecodeUtf8'cpu'arguments'intercept
  | DecodeUtf8'cpu'arguments'slope
  | DecodeUtf8'memory'arguments'intercept
  | DecodeUtf8'memory'arguments'slope
  | DivideInteger'cpu'arguments'constant
  | DivideInteger'cpu'arguments'model'arguments'intercept
  | DivideInteger'cpu'arguments'model'arguments'slope
  | DivideInteger'memory'arguments'intercept
  | DivideInteger'memory'arguments'minimum
  | DivideInteger'memory'arguments'slope
  | EncodeUtf8'cpu'arguments'intercept
  | EncodeUtf8'cpu'arguments'slope
  | EncodeUtf8'memory'arguments'intercept
  | EncodeUtf8'memory'arguments'slope
  | EqualsByteString'cpu'arguments'constant
  | EqualsByteString'cpu'arguments'intercept
  | EqualsByteString'cpu'arguments'slope
  | EqualsByteString'memory'arguments
  | EqualsData'cpu'arguments'intercept
  | EqualsData'cpu'arguments'slope
  | EqualsData'memory'arguments
  | EqualsInteger'cpu'arguments'intercept
  | EqualsInteger'cpu'arguments'slope
  | EqualsInteger'memory'arguments
  | EqualsString'cpu'arguments'constant
  | EqualsString'cpu'arguments'intercept
  | EqualsString'cpu'arguments'slope
  | EqualsString'memory'arguments
  | FstPair'cpu'arguments
  | FstPair'memory'arguments
  | HeadList'cpu'arguments
  | HeadList'memory'arguments
  | IData'cpu'arguments
  | IData'memory'arguments
  | IfThenElse'cpu'arguments
  | IfThenElse'memory'arguments
  | IndexByteString'cpu'arguments
  | IndexByteString'memory'arguments
  | LengthOfByteString'cpu'arguments
  | LengthOfByteString'memory'arguments
  | LessThanByteString'cpu'arguments'intercept
  | LessThanByteString'cpu'arguments'slope
  | LessThanByteString'memory'arguments
  | LessThanEqualsByteString'cpu'arguments'intercept
  | LessThanEqualsByteString'cpu'arguments'slope
  | LessThanEqualsByteString'memory'arguments
  | LessThanEqualsInteger'cpu'arguments'intercept
  | LessThanEqualsInteger'cpu'arguments'slope
  | LessThanEqualsInteger'memory'arguments
  | LessThanInteger'cpu'arguments'intercept
  | LessThanInteger'cpu'arguments'slope
  | LessThanInteger'memory'arguments
  | ListData'cpu'arguments
  | ListData'memory'arguments
  | MapData'cpu'arguments
  | MapData'memory'arguments
  | MkCons'cpu'arguments
  | MkCons'memory'arguments
  | MkNilData'cpu'arguments
  | MkNilData'memory'arguments
  | MkNilPairData'cpu'arguments
  | MkNilPairData'memory'arguments
  | MkPairData'cpu'arguments
  | MkPairData'memory'arguments
  | ModInteger'cpu'arguments'constant
  | ModInteger'cpu'arguments'model'arguments'intercept
  | ModInteger'cpu'arguments'model'arguments'slope
  | ModInteger'memory'arguments'intercept
  | ModInteger'memory'arguments'minimum
  | ModInteger'memory'arguments'slope
  | MultiplyInteger'cpu'arguments'intercept
  | MultiplyInteger'cpu'arguments'slope
  | MultiplyInteger'memory'arguments'intercept
  | MultiplyInteger'memory'arguments'slope
  | NullList'cpu'arguments
  | NullList'memory'arguments
  | QuotientInteger'cpu'arguments'constant
  | QuotientInteger'cpu'arguments'model'arguments'intercept
  | QuotientInteger'cpu'arguments'model'arguments'slope
  | QuotientInteger'memory'arguments'intercept
  | QuotientInteger'memory'arguments'minimum
  | QuotientInteger'memory'arguments'slope
  | RemainderInteger'cpu'arguments'constant
  | RemainderInteger'cpu'arguments'model'arguments'intercept
  | RemainderInteger'cpu'arguments'model'arguments'slope
  | RemainderInteger'memory'arguments'intercept
  | RemainderInteger'memory'arguments'minimum
  | RemainderInteger'memory'arguments'slope
  | SerialiseData'cpu'arguments'intercept
  | SerialiseData'cpu'arguments'slope
  | SerialiseData'memory'arguments'intercept
  | SerialiseData'memory'arguments'slope
  | Sha2_256'cpu'arguments'intercept
  | Sha2_256'cpu'arguments'slope
  | Sha2_256'memory'arguments
  | Sha3_256'cpu'arguments'intercept
  | Sha3_256'cpu'arguments'slope
  | Sha3_256'memory'arguments
  | SliceByteString'cpu'arguments'intercept
  | SliceByteString'cpu'arguments'slope
  | SliceByteString'memory'arguments'intercept
  | SliceByteString'memory'arguments'slope
  | SndPair'cpu'arguments
  | SndPair'memory'arguments
  | SubtractInteger'cpu'arguments'intercept
  | SubtractInteger'cpu'arguments'slope
  | SubtractInteger'memory'arguments'intercept
  | SubtractInteger'memory'arguments'slope
  | TailList'cpu'arguments
  | TailList'memory'arguments
  | Trace'cpu'arguments
  | Trace'memory'arguments
  | UnBData'cpu'arguments
  | UnBData'memory'arguments
  | UnConstrData'cpu'arguments
  | UnConstrData'memory'arguments
  | UnIData'cpu'arguments
  | UnIData'memory'arguments
  | UnListData'cpu'arguments
  | UnListData'memory'arguments
  | UnMapData'cpu'arguments
  | UnMapData'memory'arguments
  | VerifyEcdsaSecp256k1Signature'cpu'arguments
  | VerifyEcdsaSecp256k1Signature'memory'arguments
  | VerifyEd25519Signature'cpu'arguments'intercept
  | VerifyEd25519Signature'cpu'arguments'slope
  | VerifyEd25519Signature'memory'arguments
  | VerifySchnorrSecp256k1Signature'cpu'arguments'intercept
  | VerifySchnorrSecp256k1Signature'cpu'arguments'slope
  | VerifySchnorrSecp256k1Signature'memory'arguments
    deriving stock (Eq, Ord, Enum, Ix, Bounded, Generic)
    deriving IsParamName via (GenericParamName ParamName)

{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and are expected to appear in correct order.
-}
mkEvaluationContext :: MonadError CostModelApplyError m => [Integer] -> m EvaluationContext
mkEvaluationContext = mkDynEvaluationContext . toCostModelParams <=< tagWithParamNames @ParamName
