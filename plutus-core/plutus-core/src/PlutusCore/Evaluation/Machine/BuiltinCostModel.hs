{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData           #-}
-- So that we don't spend a lot of time optimizing loads of Core whose performance doesn't matter.
{-# OPTIONS_GHC -O0               #-}

module PlutusCore.Evaluation.Machine.BuiltinCostModel
    ( BuiltinCostModel
    , BuiltinCostModelBase(..)
    , CostingFun(..)
    , ModelAddedSizes(..)
    , ModelSubtractedSizes(..)
    , ModelConstantOrLinear(..)
    , ModelConstantOrTwoArguments(..)
    , ModelLinearSize(..)
    , ModelMultipliedSizes(..)
    , ModelMinSize(..)
    , ModelMaxSize(..)
    , ModelOneArgument(..)
    , ModelTwoArguments(..)
    , ModelThreeArguments(..)
    , ModelFourArguments(..)
    , ModelFiveArguments(..)
    , ModelSixArguments(..)
    , runCostingFunOneArgument
    , runCostingFunTwoArguments
    , runCostingFunThreeArguments
    , runCostingFunFourArguments
    , runCostingFunFiveArguments
    , runCostingFunSixArguments
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
import Data.Default.Class
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

-- | The main model which contains all data required to predict the cost of
-- builtin functions. See 'CostModelGeneration.md' for how this is
-- generated. Calibrated for the CEK machine.

{- | Many of the builtins have simple costs in for certain combinations of
   arguments but more complicated costs for other combinations: for example,
   equalsByteString will return imemdiately if the arguments have different
   lengths, and divideInteger a b will return immediately if a<b.  This type
   allows us to say exactly where the cost model applies (for a small selection
   of common situations) and only run the full costing function if necessary,
   returning a small cost (currently zero) otherwise. This is also helpful
   because we can't fit a sensible model to something like divideInteger, where
   costs really are zero above the diagonal but very complicated below it).
-}
data Support
    = Everywhere
    | OnDiagonal
    | BelowOrOnDiagonal
    | AboveOrOnDiagonal
    deriving stock (Show, Eq, Generic, Lift)
    deriving anyclass (NFData)

data BuiltinCostModelBase f =
    BuiltinCostModelBase
    {
      -- Integers
      paramAddInteger                      :: f ModelTwoArguments
    , paramSubtractInteger                 :: f ModelTwoArguments
    , paramMultiplyInteger                 :: f ModelTwoArguments
    , paramDivideInteger                   :: f ModelTwoArguments
    , paramQuotientInteger                 :: f ModelTwoArguments
    , paramRemainderInteger                :: f ModelTwoArguments
    , paramModInteger                      :: f ModelTwoArguments
    , paramEqualsInteger                   :: f ModelTwoArguments
    , paramLessThanInteger                 :: f ModelTwoArguments
    , paramLessThanEqualsInteger           :: f ModelTwoArguments
    -- Bytestrings
    , paramAppendByteString                :: f ModelTwoArguments
    , paramConsByteString                  :: f ModelTwoArguments
    , paramSliceByteString                 :: f ModelThreeArguments
    , paramLengthOfByteString              :: f ModelOneArgument
    , paramIndexByteString                 :: f ModelTwoArguments
    , paramEqualsByteString                :: f ModelTwoArguments
    , paramLessThanByteString              :: f ModelTwoArguments
    , paramLessThanEqualsByteString        :: f ModelTwoArguments
    -- Cryptography and hashes
    , paramSha2_256                        :: f ModelOneArgument
    , paramSha3_256                        :: f ModelOneArgument
    , paramBlake2b_256                     :: f ModelOneArgument
    , paramVerifySignature                 :: f ModelThreeArguments
    , paramVerifyEcdsaSecp256k1Signature   :: f ModelThreeArguments
    , paramVerifySchnorrSecp256k1Signature :: f ModelThreeArguments

    -- Strings
    , paramAppendString                    :: f ModelTwoArguments
    , paramEqualsString                    :: f ModelTwoArguments
    , paramEncodeUtf8                      :: f ModelOneArgument
    , paramDecodeUtf8                      :: f ModelOneArgument
    -- Bool
    , paramIfThenElse                      :: f ModelThreeArguments
    -- Unit
    , paramChooseUnit                      :: f ModelTwoArguments
    -- Tracing
    , paramTrace                           :: f ModelTwoArguments
    -- Pairs
    , paramFstPair                         :: f ModelOneArgument
    , paramSndPair                         :: f ModelOneArgument
    -- Lists
    , paramChooseList                      :: f ModelThreeArguments
    , paramMkCons                          :: f ModelTwoArguments
    , paramHeadList                        :: f ModelOneArgument
    , paramTailList                        :: f ModelOneArgument
    , paramNullList                        :: f ModelOneArgument
    -- Data
    , paramChooseData                      :: f ModelSixArguments
    , paramConstrData                      :: f ModelTwoArguments
    , paramMapData                         :: f ModelOneArgument
    , paramListData                        :: f ModelOneArgument
    , paramIData                           :: f ModelOneArgument
    , paramBData                           :: f ModelOneArgument
    , paramUnConstrData                    :: f ModelOneArgument
    , paramUnMapData                       :: f ModelOneArgument
    , paramUnListData                      :: f ModelOneArgument
    , paramUnIData                         :: f ModelOneArgument
    , paramUnBData                         :: f ModelOneArgument
    , paramEqualsData                      :: f ModelTwoArguments
    -- Misc constructors
    , paramMkPairData                      :: f ModelTwoArguments
    , paramMkNilData                       :: f ModelOneArgument
    , paramMkNilPairData                   :: f ModelOneArgument
    , paramSerialiseData                   :: f ModelOneArgument
    }
    deriving stock (Generic)
    deriving anyclass (FunctorB, TraversableB, ConstraintsB)

deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", LowerIntialCharacter)]
             (BuiltinCostModelBase CostingFun) instance ToJSON (BuiltinCostModelBase CostingFun)
deriving via CustomJSON '[FieldLabelModifier (StripPrefix "param", LowerIntialCharacter)]
             (BuiltinCostModelBase CostingFun) instance FromJSON (BuiltinCostModelBase CostingFun)

-- | Same as 'CostingFun' but maybe missing.
-- We could use 'Compose Maybe CostinFun' instead but we would then need an orphan ToJSON instance.
newtype MCostingFun a = MCostingFun (Maybe (CostingFun a))
    deriving newtype (ToJSON)
    deriving (Semigroup, Monoid) via (Alt Maybe (CostingFun a)) -- for mempty == MCostingFun Nothing

-- Omit generating JSON for any costing functions that have not been set (are missing).
deriving via CustomJSON '[OmitNothingFields, FieldLabelModifier (StripPrefix "param", LowerIntialCharacter)]
             (BuiltinCostModelBase MCostingFun) instance ToJSON (BuiltinCostModelBase MCostingFun)

-- Needed to help derive various instances for BuiltinCostModelBase
type AllArgumentModels (constraint :: Kind.Type -> Kind.Constraint) f =
    ( constraint (f ModelOneArgument)
    , constraint (f ModelTwoArguments)
    , constraint (f ModelThreeArguments)
    , constraint (f ModelFourArguments)
    , constraint (f ModelFiveArguments)
    , constraint (f ModelSixArguments))

-- HLS doesn't like the AllBF from Barbies.
deriving anyclass instance AllArgumentModels NFData  f => NFData  (BuiltinCostModelBase f)
deriving anyclass instance AllArgumentModels Default f => Default (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Lift    f => Lift    (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Show    f => Show    (BuiltinCostModelBase f)
deriving stock instance AllArgumentModels Eq      f => Eq      (BuiltinCostModelBase f)
