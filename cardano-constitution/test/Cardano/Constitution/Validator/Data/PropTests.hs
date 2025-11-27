-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Constitution.Validator.Data.PropTests
  ( tests
  ) where

import Cardano.Constitution.Data.Validator
import Cardano.Constitution.Validator.Data.TestsCommon
import Data.Map.Strict qualified as M
import Helpers.TestBuilders
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx as Tx
import PlutusTx.Builtins.Internal as BI (BuiltinUnit (..))
import UntypedPlutusCore as UPLC

import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.QuickCheck

{-| Tests that all `ConstitutionValidator` implementations return the same output
for the same random input **when run inside Haskell**. -}
prop_hsValidatorsAgreeAll :: V3.ArbitraryContext -> Property
prop_hsValidatorsAgreeAll = hsValidatorsAgree $ M.elems defaultValidators

{-| Test (in Haskell) each validator in the list with the same random input,
and make sure that all of the validators return the same result. -}
hsValidatorsAgree
  :: [ConstitutionValidator]
  -> (V3.ArbitraryContext -> Property)
hsValidatorsAgree vs ctx = go vs
  where
    go (v1 : v2 : vrest) =
      ioProperty
        ( (===)
            <$> tryApplyOnData v1 ctx
            <*> tryApplyOnData v2 ctx
        )
        .&&. if null vrest
          then property True -- done
          else go (v2 : vrest)
    go _ = property False -- needs at least two validators, otherwise the property fails

{-  Given some random input, running each validator offline (in Haskell) and online (in Tx) yields the same result.
This is different from `prop_hsValidatorsAgree`: it evals each validator individually
with two different eval machines (Hs/Tx) and checks that the machines agree.
-}
prop_hsAgreesWithTxAll :: Property
prop_hsAgreesWithTxAll = conjoin $ hsAgreesWithTx <$> M.elems defaultValidatorsWithCodes

hsAgreesWithTx
  :: (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> (V3.ArbitraryContext -> Property)
hsAgreesWithTx (vHs, vCode) ctx = ioProperty $ do
  resHs <- tryApplyOnData vHs ctx
  let vPs =
        _progTerm $
          getPlcNoAnn $
            vCode
              `unsafeApplyCode` liftCode110 (unsafeFromBuiltinData . toBuiltinData $ ctx)
      resPs = runCekRes vPs

  pure $ case (resHs, resPs) of
    (Left _, Left _) -> property True
    (Right okHs, Right okPs) -> liftCode110Norm okHs === okPs
    _ -> property False

tests :: TestTreeWithTestState
tests =
  testGroup' "Property" $
    fmap
      const
      [ -- TODO This test is flaky and needs to be fixed before re-enabling
        ignoreTest $ testProperty "hsValidatorsAgreeAll" prop_hsValidatorsAgreeAll
      , testProperty "hsAgreesWithTxAll" prop_hsAgreesWithTxAll
      ]

-- for testing purposes
instance Eq BI.BuiltinUnit where
  -- not sure if needed to patternmatch everything here
  BI.BuiltinUnit () == BI.BuiltinUnit () = True
