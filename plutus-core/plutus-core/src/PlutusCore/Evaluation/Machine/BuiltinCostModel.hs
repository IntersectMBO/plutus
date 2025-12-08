-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- So that we don't spend a lot of time optimizing loads of Core whose performance doesn't matter.
{-# OPTIONS_GHC -O0 #-}

module PlutusCore.Evaluation.Machine.BuiltinCostModel
  ( BuiltinCostModel
  , BuiltinCostModelBase (..)
  , CostingFun (..)
  , UnimplementedCostingFun (..)
  , Intercept (..)
  , Slope (..)
  , Coefficient0 (..)
  , Coefficient1 (..)
  , Coefficient2 (..)
  , Coefficient00 (..)
  , Coefficient10 (..)
  , Coefficient01 (..)
  , Coefficient20 (..)
  , Coefficient11 (..)
  , Coefficient02 (..)
  , Coefficient12 (..)
  , OneVariableLinearFunction (..)
  , OneVariableQuadraticFunction (..)
  , TwoVariableLinearFunction (..)
  , TwoVariableQuadraticFunction (..)
  , ExpModCostingFunction (..)
  , ModelSubtractedSizes (..)
  , ModelConstantOrOneArgument (..)
  , ModelConstantOrTwoArguments (..)
  , ModelConstantOrLinear (..) -- Deprecated: see Note [Backward compatibility for costing functions]
  , ModelOneArgument (..)
  , ModelTwoArguments (..)
  , ModelThreeArguments (..)
  , ModelFourArguments (..)
  , ModelFiveArguments (..)
  , ModelSixArguments (..)
  , ModelSevenArguments (..)
  , runCostingFunOneArgument
  , runCostingFunTwoArguments
  , runCostingFunThreeArguments
  , runCostingFunFourArguments
  , runCostingFunFiveArguments
  , runCostingFunSixArguments
  , runCostingFunSevenArguments
  , Hashable
  , MCostingFun (..)
  )
where

import PlutusPrelude hiding (toList)

import PlutusCore.Evaluation.Machine.CostingFun.Core
import PlutusCore.Evaluation.Machine.CostingFun.JSON ()
import PlutusCore.Evaluation.Machine.ExBudget

import Barbies
import Data.Aeson
import Data.Kind qualified as Kind
import Data.Monoid
import Deriving.Aeson
import Language.Haskell.TH.Syntax hiding (Name, newName)

type BuiltinCostModel = BuiltinCostModelBase CostingFun

-- See  Note [Budgeting units] in ExBudgeting.hs

-- If the types here change there may be difficulties compiling this file
-- because it doesn't match builtinCostModel.json (which is parsed during
-- compilation).  In that case, manually change the JSON to match or do what it
-- says in Note [Modifying the cost model] in ExBudgetingDefaults.hs.

{-| The main model which contains all data required to predict the cost of
builtin functions. See 'CostModelGeneration.md' for how this is
generated. Calibrated for the CEK machine. -}
data BuiltinCostModelBase f
  = BuiltinCostModelBase
  { -- Integers
    paramAddInteger :: f ModelTwoArguments
  , paramSubtractInteger :: f ModelTwoArguments
  , paramMultiplyInteger :: f ModelTwoArguments
  , paramDivideInteger :: f ModelTwoArguments
  , paramQuotientInteger :: f ModelTwoArguments
  , paramRemainderInteger :: f ModelTwoArguments
  , paramModInteger :: f ModelTwoArguments
  , paramEqualsInteger :: f ModelTwoArguments
  , paramLessThanInteger :: f ModelTwoArguments
  , paramLessThanEqualsInteger :: f ModelTwoArguments
  , -- Bytestrings
    paramAppendByteString :: f ModelTwoArguments
  , paramConsByteString :: f ModelTwoArguments
  , paramSliceByteString :: f ModelThreeArguments
  , paramLengthOfByteString :: f ModelOneArgument
  , paramIndexByteString :: f ModelTwoArguments
  , paramEqualsByteString :: f ModelTwoArguments
  , paramLessThanByteString :: f ModelTwoArguments
  , paramLessThanEqualsByteString :: f ModelTwoArguments
  , -- Cryptography and hashes
    paramSha2_256 :: f ModelOneArgument
  , paramSha3_256 :: f ModelOneArgument
  , paramBlake2b_256 :: f ModelOneArgument
  , paramVerifyEd25519Signature :: f ModelThreeArguments
  , paramVerifyEcdsaSecp256k1Signature :: f ModelThreeArguments
  , paramVerifySchnorrSecp256k1Signature :: f ModelThreeArguments
  , -- Strings
    paramAppendString :: f ModelTwoArguments
  , paramEqualsString :: f ModelTwoArguments
  , paramEncodeUtf8 :: f ModelOneArgument
  , paramDecodeUtf8 :: f ModelOneArgument
  , -- Bool
    paramIfThenElse :: f ModelThreeArguments
  , -- Unit
    paramChooseUnit :: f ModelTwoArguments
  , -- Tracing
    paramTrace :: f ModelTwoArguments
  , -- Pairs
    paramFstPair :: f ModelOneArgument
  , paramSndPair :: f ModelOneArgument
  , -- Lists
    paramChooseList :: f ModelThreeArguments
  , paramMkCons :: f ModelTwoArguments
  , paramHeadList :: f ModelOneArgument
  , paramTailList :: f ModelOneArgument
  , paramNullList :: f ModelOneArgument
  , -- Data
    paramChooseData6 :: f ModelSixArguments
  , paramChooseData7 :: f ModelSevenArguments
  , paramConstrData :: f ModelTwoArguments
  , paramMapData :: f ModelOneArgument
  , paramListData :: f ModelOneArgument
  , paramIData :: f ModelOneArgument
  , paramBData :: f ModelOneArgument
  , paramUnConstrData :: f ModelOneArgument
  , paramUnMapData :: f ModelOneArgument
  , paramUnListData :: f ModelOneArgument
  , paramUnIData :: f ModelOneArgument
  , paramUnBData :: f ModelOneArgument
  , paramEqualsData :: f ModelTwoArguments
  , -- Misc constructors
    paramMkPairData :: f ModelTwoArguments
  , paramMkNilData :: f ModelOneArgument
  , paramMkNilPairData :: f ModelOneArgument
  , paramSerialiseData :: f ModelOneArgument
  , -- BLS12-381
    paramBls12_381_G1_add :: f ModelTwoArguments
  , paramBls12_381_G1_neg :: f ModelOneArgument
  , paramBls12_381_G1_scalarMul :: f ModelTwoArguments
  , paramBls12_381_G1_multiScalarMul :: f ModelTwoArguments
  , paramBls12_381_G1_equal :: f ModelTwoArguments
  , paramBls12_381_G1_compress :: f ModelOneArgument
  , paramBls12_381_G1_uncompress :: f ModelOneArgument
  , paramBls12_381_G1_hashToGroup :: f ModelTwoArguments
  , paramBls12_381_G2_add :: f ModelTwoArguments
  , paramBls12_381_G2_neg :: f ModelOneArgument
  , paramBls12_381_G2_scalarMul :: f ModelTwoArguments
  , paramBls12_381_G2_equal :: f ModelTwoArguments
  , paramBls12_381_G2_multiScalarMul :: f ModelTwoArguments
  , paramBls12_381_G2_compress :: f ModelOneArgument
  , paramBls12_381_G2_uncompress :: f ModelOneArgument
  , paramBls12_381_G2_hashToGroup :: f ModelTwoArguments
  , paramBls12_381_millerLoop :: f ModelTwoArguments
  , paramBls12_381_mulMlResult :: f ModelTwoArguments
  , paramBls12_381_finalVerify :: f ModelTwoArguments
  , -- Keccak_256, Blake2b_224
    paramKeccak_256 :: f ModelOneArgument
  , paramBlake2b_224 :: f ModelOneArgument
  , -- Bitwise operations
    paramIntegerToByteString :: f ModelThreeArguments
  , paramByteStringToInteger :: f ModelTwoArguments
  , paramAndByteString :: f ModelThreeArguments
  , paramOrByteString :: f ModelThreeArguments
  , paramXorByteString :: f ModelThreeArguments
  , paramComplementByteString :: f ModelOneArgument
  , paramReadBit :: f ModelTwoArguments
  , paramWriteBits :: f ModelThreeArguments
  , paramReplicateByte :: f ModelTwoArguments
  , paramShiftByteString :: f ModelTwoArguments
  , paramRotateByteString :: f ModelTwoArguments
  , paramCountSetBits :: f ModelOneArgument
  , paramFindFirstSetBit :: f ModelOneArgument
  , -- Ripemd_160
    paramRipemd_160 :: f ModelOneArgument
  , -- Batch 6
    paramExpModInteger :: f ModelThreeArguments
  , paramDropList :: f ModelTwoArguments
  , -- Arrays
    paramLengthOfArray :: f ModelOneArgument
  , paramListToArray :: f ModelOneArgument
  , paramIndexArray :: f ModelTwoArguments
  , -- Builtin values
    paramLookupCoin :: f ModelThreeArguments
  , paramValueContains :: f ModelTwoArguments
  , paramValueData :: f ModelOneArgument
  , paramUnValueData :: f ModelOneArgument
  }
  deriving stock (Generic)
  deriving anyclass (FunctorB, TraversableB, ConstraintsB)

deriving via
  CustomJSON
    '[FieldLabelModifier (StripPrefix "param", LowerInitialCharacter)]
    (BuiltinCostModelBase CostingFun)
  instance
    ToJSON (BuiltinCostModelBase CostingFun)
deriving via
  CustomJSON
    '[FieldLabelModifier (StripPrefix "param", LowerInitialCharacter)]
    (BuiltinCostModelBase CostingFun)
  instance
    FromJSON (BuiltinCostModelBase CostingFun)

{-| Same as 'CostingFun' but maybe missing.
We could use 'Compose Maybe CostinFun' instead but we would then need an orphan ToJSON instance. -}
newtype MCostingFun a = MCostingFun (Maybe (CostingFun a))
  deriving newtype (ToJSON)
  deriving (Semigroup, Monoid) via (Alt Maybe (CostingFun a)) -- for mempty == MCostingFun Nothing

-- Omit generating JSON for any costing functions that have not been set (are missing).
deriving via
  CustomJSON
    '[OmitNothingFields, FieldLabelModifier (StripPrefix "param", LowerInitialCharacter)]
    (BuiltinCostModelBase MCostingFun)
  instance
    ToJSON (BuiltinCostModelBase MCostingFun)

-- Needed to help derive various instances for BuiltinCostModelBase
type AllArgumentModels (constraint :: Kind.Type -> Kind.Constraint) f =
  ( constraint (f ModelOneArgument)
  , constraint (f ModelTwoArguments)
  , constraint (f ModelThreeArguments)
  , constraint (f ModelFourArguments)
  , constraint (f ModelFiveArguments)
  , constraint (f ModelSixArguments)
  , constraint (f ModelSevenArguments)
  )

-- HLS doesn't like the AllBF from Barbies.
deriving anyclass instance AllArgumentModels NFData f => NFData (BuiltinCostModelBase f)
deriving anyclass instance AllArgumentModels Default f => Default (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Lift f => Lift (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Show f => Show (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Eq f => Eq (BuiltinCostModelBase f)
