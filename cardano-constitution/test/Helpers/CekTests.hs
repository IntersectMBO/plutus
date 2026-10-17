module Helpers.CekTests
  ( hsValidatorsAgreesAndPassAll
  , hsValidatorsAgreesAndErrAll
  , dataValidatorsAgreeAndPassAll
  , dataValidatorsAgreeAndErrAll
  , hsAgreesWithTx
  , dataHsAgreesWithTx
  , hsAgreesWithTxBool
  ) where

import Cardano.Constitution.Data.Validator qualified as DV
import Cardano.Constitution.Validator
import Cardano.Constitution.Validator.TestsCommon
import Control.Exception (ErrorCall, evaluate, try)
import Data.Foldable (for_)
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx as Tx
import PlutusTx.Builtins.Internal (BuiltinUnit)
import Test.Tasty.HUnit (Assertion, assertBool)
import Test.Tasty.QuickCheck
import UntypedPlutusCore as UPLC

hsValidatorsAgreesAndPassAll
  , hsValidatorsAgreesAndErrAll
    :: [(ConstitutionValidator, CompiledCode ConstitutionValidator)]
    -> V3.FakeProposedContext
    -> Assertion
hsValidatorsAgreesAndPassAll vs ctx =
  for_ vs $ \v ->
    validatorAgreesWithTx (Just True) v (toBuiltinData ctx)
      >>= assertBool "Expected both Haskell and CEK executions to pass"
hsValidatorsAgreesAndErrAll vs ctx =
  for_ vs $ \v ->
    validatorAgreesWithTx (Just False) v (toBuiltinData ctx)
      >>= assertBool "Expected both Haskell and CEK executions to fail"

dataValidatorsAgreeAndPassAll
  , dataValidatorsAgreeAndErrAll
    :: [(DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)]
    -> V3.FakeProposedContext
    -> Assertion
dataValidatorsAgreeAndPassAll vs ctx =
  for_ vs $ \v ->
    validatorAgreesWithTx (Just True) v (unsafeFromBuiltinData $ toBuiltinData ctx)
      >>= assertBool "Expected both Haskell and CEK executions to pass"
dataValidatorsAgreeAndErrAll vs ctx =
  for_ vs $ \v ->
    validatorAgreesWithTx (Just False) v (unsafeFromBuiltinData $ toBuiltinData ctx)
      >>= assertBool "Expected both Haskell and CEK executions to fail"

hsAgreesWithTx
  :: (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> V3.ArbitraryContext
  -> Property
hsAgreesWithTx v ctx = ioProperty $ hsAgreesWithTxBool v ctx

dataHsAgreesWithTx
  :: (DV.ConstitutionValidator, CompiledCode DV.ConstitutionValidator)
  -> V3.ArbitraryContext
  -> Property
dataHsAgreesWithTx v ctx =
  ioProperty $ validatorAgreesWithTx Nothing v (unsafeFromBuiltinData $ toBuiltinData ctx)

hsAgreesWithTxBool
  :: ToData ctx
  => (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> ctx
  -> IO Bool
hsAgreesWithTxBool v ctx = validatorAgreesWithTx Nothing v (toBuiltinData ctx)

{-| Run the same validator in Haskell and on the CEK, requiring matching results.
An optional expectation additionally requires both executions to pass or both to fail. -}
validatorAgreesWithTx
  :: Lift DefaultUni ctx
  => Maybe Bool
  -> (ctx -> BuiltinUnit, CompiledCode (ctx -> BuiltinUnit))
  -> ctx
  -> IO Bool
validatorAgreesWithTx expectPass (vHs, vCode) ctx = do
  resHs <- try (evaluate $ vHs ctx) :: IO (Either ErrorCall BuiltinUnit)
  let vPs =
        _progTerm $
          getPlcNoAnn $
            vCode
              `unsafeApplyCode` liftCode110 ctx
      resPs = runCekRes vPs

  pure $ case (resHs, resPs) of
    (Left _, Left _) -> expectPass /= Just True
    (Right okHs, Right okPs) -> expectPass /= Just False && liftCode110Norm okHs == okPs
    _ -> False
