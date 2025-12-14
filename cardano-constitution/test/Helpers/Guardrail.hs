-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Helpers.Guardrail
  ( txFeePerByte
  , txFeeFixed
  , utxoCostPerByte
  , stakeAddressDeposit
  , stakePoolDeposit
  , minPoolCost
  , treasuryCut
  , monetaryExpansion
  , executionUnitPrices
  , minFeeRefScriptCoinsPerByte
  , maxBlockBodySize
  , maxTxSize
  , maxBlockExecutionUnits
  , maxTxExecutionUnits
  , maxBlockHeaderSize
  , stakePoolTargetNum
  , poolPledgeInfluence
  , poolRetireMaxEpoch
  , collateralPercentage
  , maxCollateralInputs
  , maxValueSize
  , guardrailsNotChecked
  , govDeposit
  , dRepDeposit
  , dRepActivity
  , dRepVotingThresholds
  , poolVotingThresholds
  , govActionLifetime
  , committeeMaxTermLimit
  , committeeMinSize
  , ignoreTestBecauseIf
  , getGuardrailTestGroup
  , getCombinedConstraintTest
  , boundaries
  , paramRange
  , getParamIx
  , getParamName
  , IntervalEnum (..)
  , Guardrail (..)
  , Scalar
  , Boundary (..)
  , Param
  , Collection
  , GenericParam (..)
  , getDomain
  , getDefaultValue
  , testSet
  , paramListTestSet
  , allParams
  , getFakeLargeParamsChange
  ) where

import Helpers.TestBuilders hiding (Range (..))

import Data.Aeson
import Data.List (foldl', sortOn)
import Helpers.Farey
import Helpers.Intervals
import PlutusTx.IsData.Class
import Test.Tasty.QuickCheck

import Helpers.Intervals qualified as I
import Test.Tasty.ExpectedFailure

import Cardano.Constitution.Config.Types (ParamKey)
import Data.Ratio
import PlutusLedgerApi.V3 (BuiltinData)

data Scalar a
data Collection a
data Param a

-- data FixedList a

data Assertion a

data Guardrail a where
  MustNotBe :: (String, String) -> RangeConstraint a -> Guardrail (Assertion a)
  Once :: Guardrail (Assertion a) -> Guardrail (Assertion a)
  Param
    :: (IntervalEnum a, ToData a, ToJSON a, Show a, HasRange a, HasDomain a, Num a, Ord a)
    => Integer -> String -> a -> [Guardrail (Assertion a)] -> Guardrail (Param (Scalar a))
  WithinDomain
    :: (IntervalEnum a, ToData a, ToJSON a, Show a, HasRange a, HasDomain a, Num a, Ord a)
    => Guardrail (Param (Scalar a)) -> (a, a) -> Guardrail (Param (Scalar a))
  ParamList
    :: (IntervalEnum a, ToData a, ToJSON a, Show a, Num a, HasRange a, Ord a, HasDomain a)
    => Integer -> String -> [Guardrail (Param (Scalar a))] -> Guardrail (Param (Collection a))

guardrailsNotChecked :: Guardrail (Param (Scalar Integer))
guardrailsNotChecked =
  Param @Integer
    999
    "guardrailsNotChecked"
    0
    [ ("PARAM-01", "Any protocol parameter that is not explicitly named in this document must not be changed by a parameter update governance action") `MustNotBe` NL 0
    , ("PARAM-02", "Where a parameter is explicitly listed in this document but no guardrails are specified, the script must not impose any constraints on changes to the parameter") `MustNotBe` NL 0
    , ("PARAM-03", "Critical protocol parameters require an SPO vote in addition to a DRep vote: SPOs must say \"yes\" with a collective support of more than 60% of all active block production stake. This is enforced by the guardrails on the `ppSecurityParam` voting threshold") `MustNotBe` NL 0
    , ("PARAM-05", "DReps must vote \"yes\" with a collective support of more than 50% of all active voting stake. This is enforced by the guardrails on the DRep voting thresholds") `MustNotBe` NL 0
    ]

txFeePerByte :: Guardrail (Param (Scalar Integer))
txFeePerByte =
  Param @Integer
    0
    "txFeePerByte"
    44
    [ ("TFPB-01", "txFeePerByte must not be lower than 30 (0.000030 ada)") `MustNotBe` NL 30
    , ("TFPB-02", "txFeePerByte must not exceed 1,000 (0.001 ada)") `MustNotBe` NG 1_000
    , ("TFPB-03", "txFeePerByte must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 5_000)

txFeeFixed :: Guardrail (Param (Scalar Integer))
txFeeFixed =
  Param @Integer
    1
    "txFeeFixed"
    155_381
    [ ("TFF-01", "txFeeFixed must not be lower than 100,000 (0.1 ada)") `MustNotBe` NL 100_000
    , ("TFF-02", "txFeeFixed must not exceed 10,000,000 (10 ada)") `MustNotBe` NG 10_000_000
    , ("TFF-03", "txFeeFixed must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-100_000, 12_000_000)

utxoCostPerByte :: Guardrail (Param (Scalar Integer))
utxoCostPerByte =
  Param @Integer
    17
    "utxoCostPerByte"
    4_310
    [ ("UCPB-01", "utxoCostPerByte must not be lower than 3,000 (0.003 ada)") `MustNotBe` NL 3_000
    , ("UCPB-02", "utxoCostPerByte must not exceed 6,500 (0.0065 ada)") `MustNotBe` NG 6_500
    , Once (("UCPB-03", "utxoCostPerByte must not be set to 0") `MustNotBe` NEQ 0)
    , ("UCPB-04", "utxoCostPerByte must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 10_000)

stakeAddressDeposit :: Guardrail (Param (Scalar Integer))
stakeAddressDeposit =
  Param @Integer
    5
    "stakeAddressDeposit"
    2_000_000
    [ ("SAD-01", "stakeAddressDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000
    , ("SAD-02", "stakeAddressDeposit must not exceed 5,000,000 (5 ada)") `MustNotBe` NG 5_000_000
    , ("SAD-03", "stakeAddressDeposit must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 10_000_000)

stakePoolDeposit :: Guardrail (Param (Scalar Integer))
stakePoolDeposit =
  Param @Integer
    6
    "stakePoolDeposit"
    500_000_000
    [ ("SPD-01", "stakePoolDeposit must not be lower than 250,000,000 (250 ada)") `MustNotBe` NL 250_000_000
    , ("SPD-02", "stakePoolDeposit must not exceed 500,000,000 (500 ada)") `MustNotBe` NG 500_000_000
    , ("SDP-03", "stakePoolDeposit must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 700_000_000)

minPoolCost :: Guardrail (Param (Scalar Integer))
minPoolCost =
  Param @Integer
    16
    "minPoolCost"
    170_000_000
    [ ("MPC-01", "minPoolCost must not be negative") `MustNotBe` NL 0
    , ("MPC-02", "minPoolCost must not exceed 500,000,000 (500 ada)") `MustNotBe` NG 500_000_000
    ]
    `WithinDomain` (-5_000, 600_000_000)

treasuryCut :: Guardrail (Param (Scalar Rational))
treasuryCut =
  Param @Rational
    11
    "treasuryCut"
    0.3
    [ ("TC-01", "treasuryCut must not be lower than 0.1 (10%)") `MustNotBe` NL 0.1
    , ("TC-02", "treasuryCut must not exceed 0.3 (30%)") `MustNotBe` NG 0.3
    , ("TC-03", "treasuryCut must not be negative") `MustNotBe` NL 0
    , ("TC-04", "treasuryCut must not exceed 1.0 (100%)") `MustNotBe` NG 1.0
    ]
    `WithinDomain` (-1.0, 1.0)

monetaryExpansion :: Guardrail (Param (Scalar Rational))
monetaryExpansion =
  Param @Rational
    10
    "monetaryExpansion"
    0.003
    [ ("ME-01", "monetaryExpansion must not exceed 0.005") `MustNotBe` NG 0.005
    , ("ME-02", "monetaryExpansion must not be lower than 0.001") `MustNotBe` NL 0.001
    , ("ME-03", "monetaryExpansion must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-1.0, 1.0)

executionUnitPrices :: Guardrail (Param (Collection Rational))
executionUnitPrices =
  ParamList @Rational
    19
    "executionUnitPrices"
    [ Param
        0
        "priceMemory"
        (577 % 10_000)
        [ ("EIUP-PM-01", "executionUnitPrices[priceMemory] must not exceed 2_000 / 10_000") `MustNotBe` NG (2_000 % 10_000)
        , ("EIUP-PM-02", "executionUnitPrices[priceMemory] must not be lower than 400 / 10_000") `MustNotBe` NL (400 % 10_000)
        ]
        `WithinDomain` (0.0, 1.0)
    , Param
        1
        "priceSteps"
        (721 % 10_000_000)
        [ ("EIUP-PS-01", "executionUnitPrices[priceSteps] must not exceed 2,000 / 10,000,000") `MustNotBe` NG (2_000 % 10_000_000)
        , ("EIUP-PS-02", "executionUnitPrices[priceSteps] must not be lower than 500 / 10,000,000") `MustNotBe` NL (500 % 10_000_000)
        ]
        `WithinDomain` (0.0, 1.0)
    ]

minFeeRefScriptCoinsPerByte :: Guardrail (Param (Scalar Rational))
minFeeRefScriptCoinsPerByte =
  Param @Rational
    33
    "minFeeRefScriptCoinsPerByte"
    1
    [ ("MFRS-01", "minFeeRefScriptCoinsPerByte must not exceed 1,000 (0.001 ada)") `MustNotBe` NG (1_000 % 1)
    , ("MFRS-02", "minFeeRefScriptCoinsPerByte must not be negative") `MustNotBe` NL (0 % 1)
    ]
    `WithinDomain` (-5_000, 10_000)

maxBlockBodySize :: Guardrail (Param (Scalar Integer))
maxBlockBodySize =
  Param @Integer
    2
    "maxBlockBodySize"
    90_112
    [ ("MBBS-01", "maxBlockBodySize must not exceed 122,880 Bytes (120KB)") `MustNotBe` NG 122_880
    , ("MBBS-02", "maxBlockBodySize must not be lower than 24,576 Bytes (24KB)") `MustNotBe` NL 24_576
    ]
    `WithinDomain` (-5_000, 200_000)

maxTxSize :: Guardrail (Param (Scalar Integer))
maxTxSize =
  Param @Integer
    3
    "maxTxSize"
    16_384
    [ ("MTS-01", "maxTxSize must not exceed 32,768 Bytes (32KB)") `MustNotBe` NG 32_768
    , ("MTS-02", "maxTxSize must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 50_000)

maxBlockExecutionUnits :: Guardrail (Param (Collection Integer))
maxBlockExecutionUnits =
  ParamList @Integer
    21
    "maxBlockExecutionUnits"
    [ Param
        0
        "memory"
        62_000_000
        [ ("MBEU-M-01", "maxBlockExecutionUnits[memory] must not exceed 120,000,000 units") `MustNotBe` NG 120_000_000
        , ("MBEU-M-02", "maxBlockExecutionUnits[memory] must not be negative") `MustNotBe` NL 0
        ]
        `WithinDomain` (-100, 200_000_000)
    , Param
        1
        "steps"
        20_000_000_000
        [ ("MBEU-S-01", "maxBlockExecutionUnits[steps] must not exceed 40,000,000,000 (40Bn) units") `MustNotBe` NG 40_000_000_000
        , ("MBEU-S-02", "maxBlockExecutionUnits[steps] must not be negative") `MustNotBe` NL 0
        ]
        `WithinDomain` (-100, 50_000_000_000)
    ]

maxTxExecutionUnits :: Guardrail (Param (Collection Integer))
maxTxExecutionUnits =
  ParamList
    20
    "maxTxExecutionUnits"
    [ Param
        0
        "mem"
        20_000_000
        [ ("MTEU-M-01", "maxTxExecutionUnits[memory] must not exceed 40,000,000 units") `MustNotBe` NG 40_000_000
        , ("MTEU-M-02", "maxTxExecutionUnits[memory] must not be negative") `MustNotBe` NL 0
        ]
        `WithinDomain` (-100, 50_000_000)
    , Param
        1
        "steps"
        10_000_000_000
        [ ("MTEU-S-01", "maxTxExecutionUnits[steps] must not exceed 15,000,000,000 (15Bn) units") `MustNotBe` NG 15_000_000_000
        , ("MTEU-S-02", "maxTxExecutionUnits[steps] must not be negative") `MustNotBe` NL 0
        ]
        `WithinDomain` (-100, 16_000_000_000)
    ]

maxBlockHeaderSize :: Guardrail (Param (Scalar Integer))
maxBlockHeaderSize =
  Param @Integer
    4
    "maxBlockHeaderSize"
    1_100
    [ ("MBHS-01", "maxBlockHeaderSize must not exceed 5,000 Bytes") `MustNotBe` NG 5_000
    , ("MBHS-02", "maxBlockHeaderSize must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 10_000)

stakePoolTargetNum :: Guardrail (Param (Scalar Integer))
stakePoolTargetNum =
  Param @Integer
    8
    "stakePoolTargetNum"
    500
    [ ("SPTN-01", "stakePoolTargetNum must not be lower than 250") `MustNotBe` NL 250
    , ("SPTN-02", "stakePoolTargetNum must not exceed 2,000") `MustNotBe` NG 2_000
    , ("SPTN-03", "stakePoolTargetNum must not be negative") `MustNotBe` NL 0
    , ("SPTN-04", "stakePoolTargetNum must not be zero") `MustNotBe` NEQ 0
    ]
    `WithinDomain` (-5_000, 10_000)

poolPledgeInfluence :: Guardrail (Param (Scalar Rational))
poolPledgeInfluence =
  Param @Rational
    9
    "poolPledgeInfluence"
    0.3
    [ ("PPI-01", "poolPledgeInfluence must not be lower than 0.1") `MustNotBe` NL (1 % 10)
    , ("PPI-02", "poolPledgeInfluence must not exceed 1.0") `MustNotBe` NG (10 % 10)
    , ("PPI-03", "poolPledgeInfluence must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-1.0, 2.0)

poolRetireMaxEpoch :: Guardrail (Param (Scalar Integer))
poolRetireMaxEpoch =
  Param @Integer
    7
    "poolRetireMaxEpoch"
    18
    [ ("PRME-01", "poolRetireMaxEpoch must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 10_000)

collateralPercentage :: Guardrail (Param (Scalar Integer))
collateralPercentage =
  Param @Integer
    23
    "collateralPercentage"
    150
    [ ("CP-01", "collateralPercentage must not be lower than 100") `MustNotBe` NL 100
    , ("CP-02", "collateralPercentage must not exceed 200") `MustNotBe` NG 200
    , ("CP-03", "collateralPercentage must not be negative") `MustNotBe` NL 0
    , ("CP-04", "collateralPercentage must not be set to 0") `MustNotBe` NEQ 0
    ]
    `WithinDomain` (-100, 300)

maxCollateralInputs :: Guardrail (Param (Scalar Integer))
maxCollateralInputs =
  Param @Integer
    24
    "maxCollateralInputs"
    3
    [ ("MCI-01", "maxCollateralInputs must not be lower than 1") `MustNotBe` NL 1
    ]
    `WithinDomain` (-10, 100)

maxValueSize :: Guardrail (Param (Scalar Integer))
maxValueSize =
  Param @Integer
    22
    "maxValueSize"
    5_000
    [ ("MVS-01", "maxValueSize must not exceed 12,288 Bytes (12KB)") `MustNotBe` NG 12_288
    , ("MVS-02", "maxValueSize must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-5_000, 20_000)

govDeposit :: Guardrail (Param (Scalar Integer))
govDeposit =
  Param @Integer
    30
    "govDeposit"
    1_000_000
    [ ("GD-01", "govDeposit must not be negative") `MustNotBe` NL 0
    , ("GD-02", "govDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000
    , ("GD-03", "govDeposit must not exceed 10,000,000,000,000 (10 Million ada)") `MustNotBe` NG 10_000_000_000_000
    ]
    `WithinDomain` (-5_000, 11_000_000_000_000)

dRepDeposit :: Guardrail (Param (Scalar Integer))
dRepDeposit =
  Param @Integer
    31
    "dRepDeposit"
    1_000_000
    [ ("DRD-01", "dRepDeposit must not be negative") `MustNotBe` NL 0
    , ("DRD-02", "dRepDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000
    , ("DRD-03", "dRepDeposit must be no more than 100,000,000,000 (100,000 ada)") `MustNotBe` NG 100_000_000_000
    ]
    `WithinDomain` (-5_000, 110_000_000_000)

dRepActivity :: Guardrail (Param (Scalar Integer))
dRepActivity =
  Param @Integer
    32
    "dRepActivity"
    25
    [ ("DRA-01", "dRepActivity must not be lower than 13 epochs (2 months)") `MustNotBe` NL 13
    , ("DRA-02", "dRepActivity must not exceed 37 epochs (6 months)") `MustNotBe` NG 37
    , ("DRA-03", "dRepActivity must not be negative") `MustNotBe` NL 0
    ]
    `WithinDomain` (-10, 100)

poolVotingThresholds :: Guardrail (Param (Collection Rational))
poolVotingThresholds =
  ParamList @Rational
    25
    "poolVotingThresholds"
    [ Param
        0
        "motionNoConfidence"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-NC-01", "No confidence action thresholds must be in the range 51%-75%")
            `MustNotBe` NL (51 % 100)
        , ("VT-NC-01b", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        1
        "committeeNormal"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-CC-01", "Update Constitutional Committee action thresholds must be in the range 51%-90%")
            `MustNotBe` NL (51 % 100)
        , ("VT-CC-01b", "Update Constitutional Committee action thresholds must be in the range 51%-90%")
            `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        2
        "committeeNoConfidence"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-CC-01", "Update Constitutional Committee action thresholds must be in the range 51%-90%")
            `MustNotBe` NL (51 % 100)
        , ("VT-CC-01b", "Update Constitutional Committee action thresholds must be in the range 51%-90%")
            `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        3
        "hardForkInitiation"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-HF-01", "Hard fork action thresholds must be in the range 51%-80%")
            `MustNotBe` NL (51 % 100)
        , ("VT-HF-01b", "Hard fork action thresholds must be in the range 51%-80%")
            `MustNotBe` NG (80 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        4
        "ppSecurityGroup"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        ]
        `WithinDomain` (0, 1.5)
    ]

dRepVotingThresholds :: Guardrail (Param (Collection Rational))
dRepVotingThresholds =
  ParamList @Rational
    26
    "dRepVotingThresholds"
    [ Param
        0
        "motionNoConfidence"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-NC-01", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100)
        , ("VT-NC-01b", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        1
        "committeeNormal"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-CC-01", "Update Constitutional Committee action thresholds must be in the range 51%-90%") `MustNotBe` NL (51 % 100)
        , ("VT-CC-01b", "Update Constitutional Committee action thresholds must be in the range 51%-90%") `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        2
        "committeeNoConfidence"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-CC-01", "Update Constitutional Committee action thresholds must be in the range 51%-90%") `MustNotBe` NL (51 % 100)
        , ("VT-CC-01b", "Update Constitutional Committee action thresholds must be in the range 51%-90%") `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        3
        "updateConstitution"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-CON-01", "New Constitution or guardrails script action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100)
        , ("VT-CON-01b", "New Constitution or guardrails script action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        4
        "hardForkInitiation"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-HF-01", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NL (51 % 100)
        , ("VT-HF-01b", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NG (80 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        5
        "ppNetworkGroup"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100)
        , ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        6
        "ppEconomicGroup"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100)
        , ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        7
        "ppTechnicalGroup"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100)
        , ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        8
        "ppGovernanceGroup"
        (4 % 5)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        , ("VT-GOV-01", "Governance parameter thresholds must be in the range 75%-90%") `MustNotBe` NL (75 % 100)
        , ("VT-GOV-01b", "Governance parameter thresholds must be in the range 75%-90%") `MustNotBe` NG (90 % 100)
        ]
        `WithinDomain` (0, 1.5)
    , Param
        9
        "treasuryWithdrawal"
        (2 % 3)
        [ ("VT-GEN-01", "All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2)
        , ("VT-GEN-01b", "All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)
        ]
        `WithinDomain` (0, 1.5)
    ]

govActionLifetime :: Guardrail (Param (Scalar Integer))
govActionLifetime =
  Param @Integer
    29
    "govActionLifetime"
    5
    [ ("GAL-01", "govActionLifetime must not be lower than 1 epoch (5 days)") `MustNotBe` NL 1
    , ("GAL-02", "govActionLifetime must not be greater than 15 epochs (75 days)") `MustNotBe` NG 15
    ]
    `WithinDomain` (-10, 100)

committeeMaxTermLimit :: Guardrail (Param (Scalar Integer))
committeeMaxTermLimit =
  Param @Integer
    28
    "committeeMaxTermLimit"
    50
    [ ("CMTL-01", "committeeMaxTermLimit must not be zero") `MustNotBe` NEQ 0
    , ("CMTL-02", "committeeMaxTermLimit must not be negative") `MustNotBe` NL 0
    , ("CMTL-03", "committeeMaxTermLimit must not be lower than 18 epochs (90 days, or approximately 3 months)") `MustNotBe` NL 18
    , ("CMTL-04", "committeeMaxTermLimit must not exceed 293 epochs (approximately 4 years)") `MustNotBe` NG 293
    ]
    `WithinDomain` (-10, 400)

committeeMinSize :: Guardrail (Param (Scalar Integer))
committeeMinSize =
  Param @Integer
    27
    "committeeMinSize"
    3
    [ ("CMS-01", "committeeMinSize must not be negative") `MustNotBe` NL 0
    , ("CMS-02", "committeeMinSize must not be lower than 3") `MustNotBe` NL 3
    , ("CMS-03", "committeeMinSize must not exceed 10") `MustNotBe` NG 10
    ]
    `WithinDomain` (-10, 50)

gStr :: [Char] -> [Char] -> [Char]
gStr g str = g ++ ": " ++ str

--------------------------------------------------------------------------------
-- | property test for each guardrail
getGuardrailTestTree'
  :: (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a)
  => (a, a)
  -> ParamId
  -> (a -> ParamValues)
  -> Guardrail (Assertion a)
  -> TestTreeWithTestState
getGuardrailTestTree' domain' paramIx toData' assertion@(MustNotBe (g, str) _) =
  testProperty' (gStr g str) $
    getGuardrailProperty domain' toData' paramIx assertion
getGuardrailTestTree' domain' paramIx toData' g@(Once guardrail) =
  testProperty' (getStr guardrail) $
    getGuardrailProperty domain' toData' paramIx g
  where
    getStr :: Guardrail (Assertion a) -> String
    getStr (MustNotBe (g', str) _) = g' ++ ": " ++ str
    getStr (Once guardrail') = getStr guardrail'

getGuardrailProperty
  :: (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a)
  => (a, a)
  -> (a -> ParamValues)
  -> ParamId
  -> Guardrail (Assertion a)
  -> PropertyWithTestState
getGuardrailProperty domain' toData' paramIx (MustNotBe _ range) =
  oneParamProp' paramIx toData' (I.rangeGen' domain' range) (not . fst)
getGuardrailProperty domain' toData' paramIx (Once guardrail) = once . getGuardrailProperty domain' toData' paramIx guardrail

getGuardrailTestGroup
  :: forall a
   . (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a, HasDomain a)
  => Guardrail (Param (Scalar a))
  -> TestTreeWithTestState
getGuardrailTestGroup gr =
  getGuardrailTestGroup' (oneParamChange $ getParamIx gr) (\ix _ -> show ix) gr

getGuardrailTestGroup'
  :: forall a
   . (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a, HasDomain a)
  => (a -> ParamValues)
  -> (Integer -> String -> String)
  -> Guardrail (Param (Scalar a))
  -> TestTreeWithTestState
getGuardrailTestGroup' toData' getParamId (Param paramIx paramName _ assertions) =
  testGroup' ("Guardrails for " ++ show paramIx) $
    map (getGuardrailTestTree' domain (getParamId paramIx paramName) toData') assertions
getGuardrailTestGroup' toData' getParamId (WithinDomain group domain') =
  propWithDomain domain' group
  where
    propWithDomain
      :: (a, a)
      -> Guardrail (Param (Scalar a))
      -> TestTreeWithTestState
    propWithDomain _ (WithinDomain group' domain'') = propWithDomain domain'' group'
    propWithDomain domain'' (Param paramIx paramName _ assertions) =
      testGroup' ("Guardrails for " ++ show paramIx) $
        map (getGuardrailTestTree' domain'' (getParamId paramIx paramName) toData') assertions

--------------------------------------------------------------------------------
-- | Combine constraints and negate one of each
getAssertionRangeAndStr :: Guardrail (Assertion a) -> (String, RangeConstraint a)
getAssertionRangeAndStr (MustNotBe (g, _) range) = (g, range)
getAssertionRangeAndStr (Once guardrail) = getAssertionRangeAndStr guardrail

negateOneConstraint
  :: [(String, RangeConstraint a)]
  -> Integer
  -> (String, [RangeConstraint a])
negateOneConstraint xs ix = foldl' f ("", []) $ zip xs [0 ..]
  where
    f
      :: (String, [RangeConstraint a])
      -> ((String, RangeConstraint a), Integer)
      -> (String, [RangeConstraint a])
    f (g, constraints) ((g', constraint), i)
      | ix == i = (prefix ++ "!" ++ g', negateRange constraint ++ constraints)
      | otherwise = (prefix ++ g', constraint : constraints)
      where
        prefix = if null g then "" else g ++ " & "

allNegationCases :: [(String, RangeConstraint a)] -> [(String, [RangeConstraint a])]
allNegationCases xs =
  map
    (negateOneConstraint xs)
    [0 .. (toInteger $ length xs - 1)]

allPositive :: [(String, RangeConstraint a)] -> (String, [RangeConstraint a])
allPositive xs = negateOneConstraint xs (-1)

ignoreTestBecauseIf :: Bool -> String -> TestTreeWithTestState -> TestTreeWithTestState
ignoreTestBecauseIf cond' str tst =
  if cond' then ignoreTestBecause str . tst else tst

expectTo
  :: (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a)
  => Bool
  -> (a, a)
  -> (a -> ParamValues)
  -> ParamId
  -> (String, [RangeConstraint a])
  -> TestTreeWithTestState
expectTo expectToSucceed domain' toData' paramId (g, constraints) ref =
  case gapsWithinRange domain' constraints of
    [] -> ignoreTestBecause "No domain to choose values from" $ testProperty g True
    xs ->
      let gen = generateFromIntervals xs
          testName =
            g
              ++ " should "
              ++ (if expectToSucceed then "succeed" else "fail")
              ++ " in range "
              ++ showIntervals xs
       in testProperty testName $ oneParamProp' paramId toData' gen ((== expectToSucceed) . fst) ref

getCombinedConstraintTest
  :: forall a
   . (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a, HasDomain a)
  => Guardrail (Param (Scalar a))
  -> TestTreeWithTestState
getCombinedConstraintTest group =
  getCombinedConstraintTest' toData' (\ix _ -> show ix) group
  where
    toData' = oneParamChange (getParamIx group)

getCombinedConstraintTest'
  :: forall a
   . (Num a, HasRange a, Ord a, ToJSON a, Show a, ToData a, HasDomain a)
  => (a -> ParamValues)
  -> (Integer -> String -> String)
  -> Guardrail (Param (Scalar a))
  -> TestTreeWithTestState
getCombinedConstraintTest' toData' getParamId (WithinDomain group domain') =
  propWithDomain domain' group
  where
    propWithDomain
      :: (a, a)
      -> Guardrail (Param (Scalar a))
      -> TestTreeWithTestState
    propWithDomain _ (WithinDomain group' domain'') = propWithDomain domain'' group'
    propWithDomain domain'' (Param paramIx paramName _ assertions) =
      let paramId = getParamId paramIx paramName
       in testGroup' ("Combined Guardrails for " ++ show paramIx) $
            -- first all positive cases
            expectTo succeed' domain'' toData' paramId (allPositive ranges)
              -- then all negation cases
              : map (expectTo fail' domain'' toData' paramId) allNegationCases'
      where
        ranges = map getAssertionRangeAndStr assertions
        allNegationCases' = allNegationCases ranges
getCombinedConstraintTest' toData' getParamId (Param paramIx name defaultValue assertions) =
  getCombinedConstraintTest'
    toData'
    getParamId
    (WithinDomain (Param paramIx name defaultValue assertions) domain)

fail', succeed' :: Bool
fail' = False
succeed' = True

getAllRangeConstraints :: Guardrail (Param (Scalar a)) -> [(String, RangeConstraint a)]
getAllRangeConstraints (WithinDomain group _) = getAllRangeConstraints group
getAllRangeConstraints (Param _ _ _ assertions) = map getAssertionRangeAndStr assertions

getDomain :: HasDomain a => Guardrail (Param (Scalar a)) -> (a, a)
getDomain (WithinDomain _ domain') = domain'
getDomain (Param {}) = domain

class IntervalEnum a where
  boundaryPred :: Boundary a -> a
  boundarySucc :: Boundary a -> a

instance IntervalEnum Integer where
  boundaryPred (Closed a) = a - 1
  boundaryPred (Open a) = a
  boundarySucc (Closed a) = a + 1
  boundarySucc (Open a) = a

instance a ~ Integer => IntervalEnum (Ratio a) where
  boundaryPred (Closed a) = fst $ findTightestRationalBounds a 64
  boundaryPred (Open a) = a
  boundarySucc (Closed a) = snd $ findTightestRationalBounds a 64
  boundarySucc (Open a) = a

boundaries
  :: (IntervalEnum a, HasDomain a, Num a, Ord a)
  => Guardrail (Param (Scalar a))
  -> (a, a)
boundaries x =
  let
    domain' = getDomain x
   in
    boundaries' domain' x

boundaries'
  :: (IntervalEnum a, Num a, Ord a)
  => (a, a)
  -> Guardrail (Param (Scalar a))
  -> (a, a)
boundaries' domain' x =
  let constraints = map snd $ getAllRangeConstraints x
      xs = gapsWithinRange domain' constraints
      (start, end) = case xs of
        [] -> error "No domain to choose values from"
        xs' -> (fst $ head xs', snd $ last xs')
   in case (start, end) of
        (Open a, Open b) -> (boundaryPred $ Open a, boundarySucc $ Open b)
        (Closed a, Open b) -> (a, boundarySucc $ Open b)
        (Open a, Closed b) -> (boundaryPred $ Open a, b)
        (Closed a, Closed b) -> (a, b)

getDefaultValue :: Guardrail (Param (Scalar a)) -> a
getDefaultValue (WithinDomain group _) = getDefaultValue group
getDefaultValue (Param _ _ defaultValue _) = defaultValue

getParamIx :: Guardrail (Param a) -> ParamIx
getParamIx (WithinDomain group _) = getParamIx group
getParamIx (Param paramIx' _ _ _) = paramIx'
getParamIx (ParamList paramIx' _ _) = paramIx'

-- getParamIx (ParamStructure paramIx' _ _) = paramIx'

getParamName :: Guardrail (Param (Scalar a)) -> String
getParamName (WithinDomain group _) = getParamName group
getParamName (Param _ name _ _) = name

paramRange
  :: (IntervalEnum a, ToData a, ToJSON a, Show a, HasRange a, HasDomain a, Num a, Ord a)
  => Guardrail (Param (Scalar a))
  -> (ParamIx, ParamRange)
paramRange a =
  let (low, high) = boundaries a
      domain' = getDomain a
      range = MkParamRangeWithinDomain (low, high) domain'
   in (getParamIx a, range)

--------------------------------------------------------------------------------
-- | test set
testSet
  :: forall a
   . ( IntervalEnum a
     , ToJSON a
     , ToData a
     , Show a
     , Num a
     , HasRange a
     , Ord a
     , HasDomain a
     )
  => Guardrail (Param (Scalar a)) -> TestTreeWithTestState
testSet guardRail =
  testSet' toData' (\ix _ -> show ix) guardRail
  where
    toData' = oneParamChange $ getParamIx guardRail

paramListTestSet
  :: forall a
   . ( IntervalEnum a
     , ToJSON a
     , ToData a
     , Show a
     , Num a
     , HasRange a
     , Ord a
     , HasDomain a
     )
  => Guardrail (Param (Collection a)) -> TestTreeWithTestState
paramListTestSet (ParamList paramIx name xs) =
  testGroup' name $ map testParam xs
  where
    testParam :: Guardrail (Param (Scalar a)) -> TestTreeWithTestState
    testParam gr = testSet' (toData' gr) getParamId gr

    toData' :: Guardrail (Param (Scalar a)) -> a -> ParamValues
    toData' gr value = [(paramIx, toValues' gr value)]

    getParamId :: Integer -> String -> String
    getParamId = getSubParamId paramIx

    toValues' :: Guardrail (Param (Scalar a)) -> a -> Printable
    toValues' selectedGr val =
      let selectedParamName = getParamName selectedGr
          xs' = flip map xs $ \x ->
            let paramName = getParamName x
             in if selectedParamName == paramName
                  then val
                  else getDefaultValue x
       in pack xs'

getSubParamId :: Integer -> Integer -> String -> String
getSubParamId paramIx subParamIx _ = show paramIx ++ "[" ++ show subParamIx ++ "]"

testSet'
  :: forall a
   . ( IntervalEnum a
     , ToJSON a
     , ToData a
     , Show a
     , Num a
     , Ord a
     , HasDomain a
     , HasRange a
     )
  => (a -> ParamValues)
  -> (Integer -> String -> String)
  -> Guardrail (Param (Scalar a))
  -> TestTreeWithTestState
testSet' toData' getParamId guardRail =
  testGroup'
    paramName
    [ testGroup'
        "In range tests"
        [ testCase' ("At upper bound (" ++ show upper ++ ")") $ unitTestTemplatePositive' paramId toData' upper
        , testCase' ("At lower bound (" ++ show lower ++ ")") $ unitTestTemplatePositive' paramId toData' lower
        , testCase' ("Current (" ++ show defaultValue ++ ")") $ unitTestTemplatePositive' paramId toData' defaultValue
        ]
    , testGroup'
        "Outside bounds"
        [ ignoreTestBecauseIf (succUpper > ed) "No upper limit" $
            testCase' ("Upper Bound (" ++ show succUpper ++ ")") $
              unitTestTemplateNegative' paramId toData' succUpper
        , ignoreTestBecauseIf (predLower < sd) "No lower limit" $
            testCase' ("Lower Bound (" ++ show predLower ++ ")") $
              unitTestTemplateNegative' paramId toData' predLower
        ]
    , getCombinedConstraintTest' toData' getParamId guardRail
    , getGuardrailTestGroup' toData' getParamId guardRail
    , testGroup'
        "Property Based Tests"
        [ testProperty' ("In range [" ++ show lower ++ ", " ++ show upper ++ "]") $
            pbtParamValidRange' paramId toData' (lower, upper)
        ]
    ]
  where
    defaultValue = getDefaultValue guardRail
    paramNo = getParamIx guardRail
    paramName = getParamName guardRail
    paramId = getParamId paramNo paramName
    (lower, upper) = boundaries guardRail
    (sd, ed) = getDomain guardRail
    predLower = boundaryPred $ Closed lower
    succUpper = boundarySucc $ Closed upper

data GenericParam = forall a. MkGenericParam (Guardrail (Param a))

allParams :: [GenericParam]
allParams =
  [ MkGenericParam txFeePerByte
  , MkGenericParam txFeeFixed
  , MkGenericParam utxoCostPerByte
  , MkGenericParam maxBlockBodySize
  , MkGenericParam maxTxSize
  , MkGenericParam maxBlockHeaderSize
  , MkGenericParam minPoolCost
  , MkGenericParam maxValueSize
  , MkGenericParam collateralPercentage
  , MkGenericParam maxCollateralInputs
  , MkGenericParam stakeAddressDeposit
  , MkGenericParam stakePoolDeposit
  , MkGenericParam poolRetireMaxEpoch
  , MkGenericParam stakePoolTargetNum
  , MkGenericParam poolPledgeInfluence
  , MkGenericParam minFeeRefScriptCoinsPerByte
  , MkGenericParam govDeposit
  , MkGenericParam dRepDeposit
  , MkGenericParam dRepActivity
  , MkGenericParam govActionLifetime
  , MkGenericParam committeeMaxTermLimit
  , MkGenericParam committeeMinSize
  , MkGenericParam monetaryExpansion
  , MkGenericParam treasuryCut
  , MkGenericParam poolVotingThresholds
  , MkGenericParam dRepVotingThresholds
  , MkGenericParam executionUnitPrices
  , MkGenericParam maxBlockExecutionUnits
  , MkGenericParam maxTxExecutionUnits
  ]

makeChangedParams
  :: (forall a. Guardrail (Param a) -> BuiltinData)
  -> [GenericParam]
  -> [(ParamKey, BuiltinData)]
makeChangedParams getValue params =
  let changedParams = map (\(MkGenericParam gr) -> (getParamIx gr, getValue gr)) params
      allCostModels' :: (ParamKey, BuiltinData) = (18, toBuiltinData allCostModels)
   in sortOn fst (allCostModels' : changedParams)

getMaxValue' :: Guardrail (Param a) -> BuiltinData
getMaxValue' gr@(Param {}) =
  let max' = 2 ^ (64 :: Int) - 1
   in toBuiltinData $ boundaryPred $ (Closed $ snd $ boundaries' (-max', max') gr)
getMaxValue' (WithinDomain gr _) = getMaxValue' gr
getMaxValue' (ParamList _ _ xs) = toBuiltinData $ map getMaxValue' xs

getFakeLargeParamsChange :: [(ParamKey, BuiltinData)]
getFakeLargeParamsChange = makeChangedParams getMaxValue' allParams
