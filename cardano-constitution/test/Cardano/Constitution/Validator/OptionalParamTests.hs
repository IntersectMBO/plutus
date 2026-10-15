-- editorconfig-checker-disable-file
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

-- | Tests for optional parameter values. See Note [Optional parameter values].
module Cardano.Constitution.Validator.OptionalParamTests
  ( tests
  ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Data.Validator qualified as DV
import Cardano.Constitution.Validator qualified as V
import Cardano.Constitution.Validator.Data.Sorted qualified as DS
import Cardano.Constitution.Validator.Data.Unsorted qualified as DU
import Cardano.Constitution.Validator.Sorted qualified as S
import Cardano.Constitution.Validator.Unsorted qualified as U
import Helpers.CekTests
import Helpers.TestBuilders
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx as Tx (CompiledCode)
import PlutusTx.Builtins as Tx (BuiltinData, mkConstr, mkI)
import PlutusTx.IsData.Class (ToData (..))
import PlutusTx.NonCanonicalRational
import PlutusTx.Ratio qualified as Tx

import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy.Char8 qualified as BSL
import Test.Tasty
import Test.Tasty.HUnit

optionalConfigJSON :: BSL.ByteString
optionalConfigJSON =
  BSL.pack $
    unlines
      [ "{"
      , "  \"0\": {"
      , "    \"type\": \"coin\","
      , "    \"predicates\": [{ \"minValue\": 30 }, { \"maxValue\": 1000 }],"
      , "    \"$comment\": \"a regular (non-optional) parameter\""
      , "  },"
      , "  \"53\": {"
      , "    \"type\": \"uint.size4\","
      , "    \"optional\": true,"
      , "    \"predicates\": [{ \"minValue\": 0 }, { \"maxValue\": 100 }],"
      , "    \"$comment\": \"an optional parameter, e.g. perasBootstrapRound\""
      , "  },"
      , "  \"54[0]\": {"
      , "    \"type\": \"integer\","
      , "    \"optional\": true,"
      , "    \"predicates\": [{ \"minValue\": 1 }],"
      , "    \"$comment\": \"an optional sub-parameter\""
      , "  },"
      , "  \"54[1]\": {"
      , "    \"type\": \"unit_interval\","
      , "    \"predicates\": [{ \"maxValue\": { \"numerator\": 1, \"denominator\": 2 } }]"
      , "  }"
      , "}"
      ]

optionalConfig :: ConstitutionConfig
optionalConfig = either error id $ Aeson.eitherDecode optionalConfigJSON

expectedConfig :: ConstitutionConfig
expectedConfig =
  ConstitutionConfig
    [ (0, ParamInteger (Predicates [(MinValue, [30]), (MaxValue, [1_000])]))
    , (53, ParamMaybe (ParamInteger (Predicates [(MinValue, [0]), (MaxValue, [100])])))
    ,
      ( 54
      , ParamList
          [ ParamMaybe (ParamInteger (Predicates [(MinValue, [1])]))
          , ParamRational (Predicates [(MaxValue, [Tx.unsafeRatio 1 2])])
          ]
      )
    ]

validators :: [(V.ConstitutionValidator, CompiledCode V.ConstitutionValidator)]
validators =
  [ (S.constitutionValidator optionalConfig, S.mkConstitutionCode optionalConfig)
  , (U.constitutionValidator optionalConfig, U.mkConstitutionCode optionalConfig)
  ]

dataValidators :: [(DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)]
dataValidators =
  [ (DS.constitutionValidator optionalConfig, DS.mkConstitutionCode optionalConfig)
  , (DU.constitutionValidator optionalConfig, DU.mkConstitutionCode optionalConfig)
  ]

positive :: [(String, V3.FakeProposedContext)]
positive =
  [ ("unset", ctx [(53, nothing)])
  , ("set-min", ctx [(53, just 0)])
  , ("set-mid", ctx [(53, just 50)])
  , ("set-max", ctx [(53, just 100)])
  , ("set-with-others", ctx [(0, int 30), (53, just 7)])
  , ("unset-with-others", ctx [(0, int 1_000), (53, nothing)])
  , ("list-elem-unset", ctx [(54, list [nothing, ratio 1 4])])
  , ("list-elem-set", ctx [(54, list [just 5, ratio 1 2])])
  , ("not-proposed", ctx [(0, int 30)])
  ]

negative :: [(String, V3.FakeProposedContext)]
negative =
  [ ("set-above-max", ctx [(53, just 101)])
  , ("set-below-min", ctx [(53, just (-1))])
  , ("set-in-range-but-other-out-of-range", ctx [(0, int 29), (53, just 7)])
  , ("unset-but-other-out-of-range", ctx [(0, int 1_001), (53, nothing)])
  , ("not-wrapped", ctx [(53, int 50)])
  , ("wrapped-in-list", ctx [(53, list [int 50])])
  , ("wrong-constr-index", ctx [(53, Tx.mkConstr 2 [])])
  , ("nothing-with-field", ctx [(53, Tx.mkConstr 1 [Tx.mkI 5])])
  , ("just-without-field", ctx [(53, Tx.mkConstr 0 [])])
  , ("just-with-extra-field", ctx [(53, Tx.mkConstr 0 [Tx.mkI 5, Tx.mkI 6])])
  , ("just-with-wrong-inner-type", ctx [(53, justData (ratio 1 2))])
  , ("just-nested", ctx [(53, justData (just 5))])
  , ("non-optional-unset", ctx [(0, nothing)])
  , ("non-optional-wrapped", ctx [(0, just 30)])
  , ("list-elem-set-out-of-range", ctx [(54, list [just 0, ratio 1 2])])
  , ("list-elem-not-wrapped", ctx [(54, list [int 5, ratio 1 2])])
  , ("list-elem-unset-but-other-out-of-range", ctx [(54, list [nothing, ratio 3 4])])
  , ("list-too-few-elems", ctx [(54, list [nothing])])
  ]

ctx :: [(ParamKey, BuiltinData)] -> V3.FakeProposedContext
ctx = V3.mkFakeParameterChangeContext

int :: Integer -> BuiltinData
int = toBuiltinData

just :: Integer -> BuiltinData
just = justData . int

justData :: BuiltinData -> BuiltinData
justData = toBuiltinData . Just

nothing :: BuiltinData
nothing = toBuiltinData (Nothing :: Maybe Integer)

ratio :: Integer -> Integer -> BuiltinData
ratio n d = toBuiltinData $ NonCanonicalRational $ Tx.unsafeRatio n d

list :: [BuiltinData] -> BuiltinData
list = toBuiltinData

tests :: TestTreeWithTestState
tests =
  testGroup' "OptionalParam" $
    fmap
      const
      [ testCase "parseConfig" $ optionalConfig @?= expectedConfig
      , testGroup "Positive" $
          fmap (\(n, c) -> testCase n $ hsValidatorsAgreesAndPassAll validators c) positive
      , testGroup "Negative" $
          fmap (\(n, c) -> testCase n $ hsValidatorsAgreesAndErrAll validators c) negative
      , testGroup "Data.Positive" $
          fmap (\(n, c) -> testCase n $ dataValidatorsAgreeAndPassAll dataValidators c) positive
      , testGroup "Data.Negative" $
          fmap (\(n, c) -> testCase n $ dataValidatorsAgreeAndErrAll dataValidators c) negative
      ]
