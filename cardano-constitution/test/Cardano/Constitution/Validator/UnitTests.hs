-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Constitution.Validator.UnitTests
  ( unitTests
  , singleParamTests
  ) where

import Cardano.Constitution.Config ()
import Cardano.Constitution.Validator
import Cardano.Constitution.Validator.TestsCommon
import Data.Map.Strict as M
import Helpers.Guardrail qualified as Guards
import Helpers.TestBuilders
import PlutusLedgerApi.V3 as V3
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx.Builtins as Tx (lengthOfByteString, serialiseData)
import PlutusTx.NonCanonicalRational
import PlutusTx.Ratio as Tx
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

-- What should be in Unit tests
-- Range tests
-- Limit tests
-- Guardrail tests

-- We should reach
-- All guardrails tested
-- All limits tested
-- MC/DC coverage

{- Note [Why de-duplicated ChangedParameters]
\**ALL** The following ScriptContext examples *MUST* be de-duplicated Lists.
Otherwise, both the sorted and unsorted scripts will produce
"wrong" results (for different reasons).
See also Guarantee(2) in README.md
-}

-- all these are actually unit tests (by using QuickCheck.once)

-- Manually kept sorted&deduped to not give false expectations upon reading the example;
-- We rely on guarantee (2) and (3) in README.md

test_pos :: TestTreeWithTestState
test_pos =
  const $
    testGroup "Positive" $
      fmap
        (\(n, c) -> testProperty n $ allVldtrsPassed (M.elems defaultValidators) c)
        [
          ( "pos1"
          , V3.mkFakeParameterChangeContext @Integer
              [ (0, 30) -- in limits
              , (1, 10_000_000) -- in limits
              , (17, 6_250) -- in limits
              ]
          )
        ,
          ( "pos2"
          , V3.mkFakeParameterChangeContext
              [ (10, NonCanonicalRational $ Tx.unsafeRatio 1 1000) -- in limits
              ]
          )
        ,
          ( "pos3"
          , V3.mkFakeParameterChangeContext
              [
                ( 19
                ,
                  [ NonCanonicalRational $ Tx.unsafeRatio 2_000 10_000 -- exmem in limits
                  , NonCanonicalRational $ Tx.unsafeRatio 500 10_000_000 -- exsteps in limits
                  ]
                )
              ]
          )
        , -- NOTE: According to constitution-script specification, this is a NOT_SPECIFIED behavior,
          -- meaning a valid const.script can decide to return success or fail either way.
          -- In reality, the ledger prohibits empty proposals, thus the const.script will not even run.
          -- Here, we only do "regression testing" of our validators, which happen to succeed
          -- for this out-of-spec behavior.

          ( "pos4"
          , V3.mkFakeParameterChangeContext @Integer
              []
          )
        ]
        -- empty params

        ++ [ testProperty "pos5" $
               forAll V3.treasuryWithdrawalsCtxGen $
                 allVldtrsPassed (M.elems defaultValidators)
           ]

test_neg :: TestTreeWithTestState
test_neg =
  const $
    testGroup "Negative" $
      fmap
        (\(n, c) -> testProperty n $ allVldtrsErred (M.elems defaultValidators) c)
        [
          ( "neg1"
          , V3.mkFakeParameterChangeContext @Integer
              [ (0, 29)
              , -- \**smaller than minbound**
                (1, 10_000_000) -- in limits
              , (2, -10_000_000_000) -- unknown param
              , (17, 6_250) -- in limits
              ]
          )
        ,
          ( "neg2"
          , V3.mkFakeParameterChangeContext @Integer
              [ (0, 29)
              , -- \**smaller than minbound**
                (1, 10_000_000) -- in limits
              , (17, 6_251)
              ]
          )
        , -- \** larger than maxbound **

          ( "neg3"
          , V3.mkFakeParameterChangeContext @Integer
              [ (-1, -1_000) -- unknown param
              ]
          )
        ,
          ( "neg4"
          , V3.mkFakeParameterChangeContext @Integer
              [ (10, 1) -- type mismatch, 10 is supposed to be Rational
              ]
          )
        ,
          ( "neg5"
          , V3.mkFakeParameterChangeContext
              [ (0, NonCanonicalRational $ Tx.unsafeRatio 1 1) -- type mismatch, 0 is supposed to be integer
              ]
          )
        ,
          ( "neg6"
          , V3.mkFakeParameterChangeContext
              [ (10, NonCanonicalRational $ Tx.unsafeRatio 0 1000) -- out of limits
              ]
          )
        ,
          ( "neg7"
          , V3.mkFakeParameterChangeContext
              [
                ( 19
                ,
                  [ NonCanonicalRational $ Tx.unsafeRatio 2_000 10_000 -- exmem in limits
                  , NonCanonicalRational $ Tx.unsafeRatio 0 10_000_000 -- exsteps out of limits
                  ]
                )
              ]
          )
        ,
          ( "neg8"
          , V3.mkFakeParameterChangeContext
              [
                ( 19
                ,
                  [ NonCanonicalRational $ Tx.unsafeRatio 2_000 10_000 -- exmem in limits
                  , NonCanonicalRational $ Tx.unsafeRatio 500 10_000_000 -- exsteps in limits
                  , NonCanonicalRational $ Tx.unsafeRatio 500 10_000_000 -- TOO MUCH SUBS in list SUPPLIED
                  ]
                )
              ]
          )
        ,
          ( "neg9"
          , V3.mkFakeParameterChangeContext
              [
                ( 19
                ,
                  [ NonCanonicalRational $ Tx.unsafeRatio 2_000 10_000 -- exmem in limits
                  -- TOO FEW SUBS in list SUPPLIED
                  ]
                )
              ]
          )
        ,
          ( "neg10"
          , V3.mkFakeParameterChangeContext @[Integer]
              [
                ( 19
                , []
                )
              ]
          )
        , -- TOO FEW SUBS in list SUPPLIED

          ( "neg11"
          , V3.mkFakeParameterChangeContext
              [
                ( 19
                , -- TOO DEEPLY NESTED

                  [
                    [ NonCanonicalRational $ Tx.unsafeRatio 2_000 10_000 -- exmem in limits
                    , NonCanonicalRational $ Tx.unsafeRatio 500 10_000_000 -- exsteps in limits
                    ]
                  ]
                )
              ]
          )
        , -- anything other than ParameterChange or TreasuryWithdrawals is `FAIL`
          ("neg12", V3.mkFakeContextFromGovAction V3.InfoAction)
        ]

test_unsorted1 :: TestTreeWithTestState
test_unsorted1 =
  const $
    testProperty "unsorted1" $
      -- unsorted fails for the right reason, sorted fails for the wrong reason
      allVldtrsErred (M.elems defaultValidators) ctx
  where
    ctx =
      V3.mkFakeParameterChangeContext @Integer
        -- deliberately kept unsorted to demonstrate the different behaviour between
        -- SORTED and UNSORTED flavour. See guarantee (3) in README.md
        [ (0, 30) -- in limits
        , (17, 6_250) -- in limits, **but breaks sorting**
        -- out of limits **should make constitution script fail**
        -- unsorted flavor fails, for the right reason (out of limits)
        -- sorted flavor fails, for the wrong reason (it ran past the config, and fail to find actualPid)
        , (1, 10_000_001)
        ]

test_unsorted2 :: TestTreeWithTestState
test_unsorted2 =
  const $
    testProperty "unsorted2" $
      -- The unsorted flavour does not depend on guarantee 3,
      -- so it can work with unsorted input map as well
      allVldtrsPassed [defaultValidators M.! "unsorted"] ctx
        -- The sorted flavour depends on guarantee 3, so it breaks with unsorted maps:
        -- the constitution scripts should fail, but they don't
        .&&. allVldtrsErred [defaultValidators M.! "sorted"] ctx
  where
    ctx =
      V3.mkFakeParameterChangeContext @Integer
        -- deliberately kept unsorted to demonstrate the different behaviour between
        -- SORTED and UNSORTED flavour. See guarantee (3) in README.md
        [ (0, 30) -- in limits
        , (17, 6_250) -- in limits, **but breaks sorting**
        -- in limits
        -- unsorted flavor passes
        -- sorted flavor fails (it ran past the config, and fail to find actualPid)
        , (1, 10_000_000)
        ]

{-| A safety check to make sure that a `ScriptContext` containg a large proposal
will not reach the  maxTxSize currently set by the chain.
In reality, proposals will not be that big.

If this size becomes so big that it is an issue, there is the option (*in certain cases only!*),
to split up such large proposal to smaller parts and submit them to the chain separately. -}
test_LargeProposalSize :: TestTreeWithTestState
test_LargeProposalSize = const $ testCaseInfo "largeProposalSize" $ do
  let largeSize =
        Tx.lengthOfByteString $
          Tx.serialiseData $
            toBuiltinData $
              V3.mkFakeParameterChangeContext Guards.getFakeLargeParamsChange
      -- current maxTxSize is 16384 Bytes set on 07/29/2020 23:44:51
      -- , but we set this limit a bit lower (to accomodate other tx costs?)
      maxTxSize = 10_000
  -- current maxTxSize
  assertBool "Large Proposal does not fit transaction-size limits." (largeSize < maxTxSize)
  pure $ "A large proposal has " <> show largeSize <> " below the limit set to " <> show maxTxSize

unitTests :: TestTreeWithTestState
unitTests =
  testGroup'
    "Unit"
    [ test_pos
    , test_neg
    , test_unsorted1
    , test_unsorted2
    , test_LargeProposalSize
    ]

singleParamTests :: TestTreeWithTestState
singleParamTests = testGroup' "Single Parameter Proposals" tests
  where
    tests = fmap f Guards.allParams

    f :: Guards.GenericParam -> TestTreeWithTestState
    f (Guards.MkGenericParam gr@(Guards.Param {})) = Guards.testSet gr
    f (Guards.MkGenericParam gr@(Guards.WithinDomain {})) = Guards.testSet gr
    f (Guards.MkGenericParam gr@(Guards.ParamList {})) = Guards.paramListTestSet gr
