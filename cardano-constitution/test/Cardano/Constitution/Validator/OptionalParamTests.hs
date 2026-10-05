-- editorconfig-checker-disable-file
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

{-| Tests for optional (`Maybe`-like) parameter values. See Note [Optional parameter values].

The default constitution config does not (yet) contain such a parameter, so these tests
use their own small config, which is parsed from JSON so as to also exercise
the `"optional": true` flag of the JSON format. The config is then applied to all 4 engines
(sorted/unsorted, and their `Data`-backed variants), both Haskell-side and compiled & run on the CEK. -}
module Cardano.Constitution.Validator.OptionalParamTests
  ( tests
  ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Data.Validator qualified as DV
import Cardano.Constitution.Validator qualified as V
import Cardano.Constitution.Validator.Data.Sorted qualified as DS
import Cardano.Constitution.Validator.Data.TestsCommon qualified as DTC
import Cardano.Constitution.Validator.Data.Unsorted qualified as DU
import Cardano.Constitution.Validator.Sorted qualified as S
import Cardano.Constitution.Validator.Unsorted qualified as U
import Helpers.CekTests
import Helpers.TestBuilders
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx as Tx (CompiledCode, getPlcNoAnn, unsafeApplyCode)
import PlutusTx.Builtins as Tx (BuiltinData, mkConstr, mkI)
import PlutusTx.IsData.Class (ToData (..), UnsafeFromData (..))
import PlutusTx.NonCanonicalRational
import PlutusTx.Ratio qualified as Tx
import UntypedPlutusCore as UPLC (_progTerm)

import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Either (isRight)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

-- | A small constitution config in the JSON format, containing optional parameters.
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

-- | What `optionalConfigJSON` is expected to parse to.
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

-- | The engines (Haskell-side, and compiled) configured with `optionalConfig`.
validators :: [(V.ConstitutionValidator, CompiledCode V.ConstitutionValidator)]
validators =
  [ (S.constitutionValidator optionalConfig, S.mkConstitutionCode optionalConfig)
  , (U.constitutionValidator optionalConfig, U.mkConstitutionCode optionalConfig)
  ]

-- | The `Data`-backed engines (Haskell-side, and compiled) configured with `optionalConfig`.
dataValidators :: [(DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)]
dataValidators =
  [ (DS.constitutionValidator optionalConfig, DS.mkConstitutionCode optionalConfig)
  , (DU.constitutionValidator optionalConfig, DU.mkConstitutionCode optionalConfig)
  ]

-- * Proposals

-- See Note [Why de-duplicated ChangedParameters]: the following are manually kept sorted & de-duplicated.

-- | Proposals that must be accepted by all engines.
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
  , -- an optional parameter that is not proposed at all, is no different than any other parameter
    ("not-proposed", ctx [(0, int 30)])
  ]

-- | Proposals that must be rejected by all engines.
negative :: [(String, V3.FakeProposedContext)]
negative =
  [ ("set-above-max", ctx [(53, just 101)])
  , ("set-below-min", ctx [(53, just (-1))])
  , ("set-in-range-but-other-out-of-range", ctx [(0, int 29), (53, just 7)])
  , ("unset-but-other-out-of-range", ctx [(0, int 1_001), (53, nothing)])
  , -- wrong encodings of an optional value
    ("not-wrapped", ctx [(53, int 50)])
  , ("wrapped-in-list", ctx [(53, list [int 50])])
  , ("wrong-constr-index", ctx [(53, Tx.mkConstr 2 [])])
  , ("nothing-with-field", ctx [(53, Tx.mkConstr 1 [Tx.mkI 5])])
  , ("just-without-field", ctx [(53, Tx.mkConstr 0 [])])
  , ("just-with-extra-field", ctx [(53, Tx.mkConstr 0 [Tx.mkI 5, Tx.mkI 6])])
  , ("just-with-wrong-inner-type", ctx [(53, justData (ratio 1 2))])
  , ("just-nested", ctx [(53, justData (just 5))])
  , -- a non-optional parameter cannot be un-set (nor wrapped)
    ("non-optional-unset", ctx [(0, nothing)])
  , ("non-optional-wrapped", ctx [(0, just 30)])
  , -- optional sub-parameters
    ("list-elem-set-out-of-range", ctx [(54, list [just 0, ratio 1 2])])
  , ("list-elem-not-wrapped", ctx [(54, list [int 5, ratio 1 2])])
  , ("list-elem-unset-but-other-out-of-range", ctx [(54, list [nothing, ratio 3 4])])
  , ("list-too-few-elems", ctx [(54, list [nothing])])
  ]

ctx :: [(ParamKey, BuiltinData)] -> V3.FakeProposedContext
ctx = V3.mkFakeParameterChangeContext

int :: Integer -> BuiltinData
int = toBuiltinData

-- | A set optional value: `Constr 0 [I n]`, same as the ledger's `StrictMaybe` encoding
just :: Integer -> BuiltinData
just = justData . int

justData :: BuiltinData -> BuiltinData
justData = toBuiltinData . Just

-- | An un-set optional value: `Constr 1 []`, same as the ledger's `StrictMaybe` encoding
nothing :: BuiltinData
nothing = toBuiltinData (Nothing :: Maybe Integer)

ratio :: Integer -> Integer -> BuiltinData
ratio n d = toBuiltinData $ NonCanonicalRational $ Tx.unsafeRatio n d

list :: [BuiltinData] -> BuiltinData
list = toBuiltinData

-- * Running the `Data`-backed engines

-- | The `Data`-backed analogues of `hsValidatorsAgreesAndPassAll` and `hsValidatorsAgreesAndErrAll`.
dataValidatorsAgreeAndPassAll
  , dataValidatorsAgreeAndErrAll
    :: [(DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)]
    -> V3.FakeProposedContext
    -> Property
dataValidatorsAgreeAndPassAll vs c = conjoin $ fmap (\v -> ioProperty $ dataValidatorAgrees v c True) vs
dataValidatorsAgreeAndErrAll vs c = conjoin $ fmap (\v -> ioProperty $ dataValidatorAgrees v c False) vs

-- | Both the Haskell-side and the compiled validator must pass (if `expectPass`), or both must err.
dataValidatorAgrees
  :: (DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)
  -> V3.FakeProposedContext
  -> Bool
  -> IO Bool
dataValidatorAgrees (vHs, vCode) c expectPass = do
  resHs <- DTC.tryApplyOnData vHs c
  let resPs =
        DTC.runCekRes $
          _progTerm $
            getPlcNoAnn $
              vCode `unsafeApplyCode` DTC.liftCode110 (unsafeFromBuiltinData $ toBuiltinData c)
  pure $ isRight resHs == expectPass && isRight resPs == expectPass

-- * Test tree

tests :: TestTreeWithTestState
tests =
  testGroup' "OptionalParam" $
    fmap
      const
      [ testCase "parseConfig" $ optionalConfig @?= expectedConfig
      , testGroup "Positive" $
          fmap (\(n, c) -> testProperty n $ once $ hsValidatorsAgreesAndPassAll validators c) positive
      , testGroup "Negative" $
          fmap (\(n, c) -> testProperty n $ once $ hsValidatorsAgreesAndErrAll validators c) negative
      , testGroup "Data.Positive" $
          fmap (\(n, c) -> testProperty n $ once $ dataValidatorsAgreeAndPassAll dataValidators c) positive
      , testGroup "Data.Negative" $
          fmap (\(n, c) -> testProperty n $ once $ dataValidatorsAgreeAndErrAll dataValidators c) negative
      ]
