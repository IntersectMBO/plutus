module Helpers.CekTests
  ( hsValidatorsAgreesAndPassAll
  , hsValidatorsAgreesAndErrAll
  , hsAgreesWithTxBool
  ) where

import Cardano.Constitution.Validator
import Cardano.Constitution.Validator.TestsCommon
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx as Tx
import Test.Tasty.QuickCheck
import UntypedPlutusCore as UPLC

hsValidatorsAgreesAndPassAll
  :: [(ConstitutionValidator, CompiledCode ConstitutionValidator)]
  -> V3.FakeProposedContext
  -> Property
hsValidatorsAgreesAndPassAll vs ctx = conjoin $ fmap (`hsValidatorsAgreesAndPass` ctx) vs

hsValidatorsAgreesAndErrAll
  :: [(ConstitutionValidator, CompiledCode ConstitutionValidator)]
  -> V3.FakeProposedContext
  -> Property
hsValidatorsAgreesAndErrAll vs ctx = conjoin $ fmap (`hsValidatorsAgreesAndErr` ctx) vs

hsAgreesWithTxBool
  :: (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> V3.FakeProposedContext
  -> IO Bool
hsAgreesWithTxBool (vHs, vCode) ctx = do
  resHs <- tryApplyOnData vHs ctx
  let vPs =
        _progTerm $
          getPlcNoAnn $
            vCode
              `unsafeApplyCode` liftCode110 (toBuiltinData ctx)
      resPs = runCekRes vPs

  pure $ case (resHs, resPs) of
    (Left _, Left _) -> True
    (Right okHs, Right okPs) -> liftCode110Norm okHs == okPs
    _ -> False

hsValidatorsAgreesAndErr
  :: (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> V3.FakeProposedContext
  -> Property
hsValidatorsAgreesAndErr (vHs, vCode) ctx = ioProperty $ do
  resHs <- tryApplyOnData vHs ctx
  let vPs =
        _progTerm $
          getPlcNoAnn $
            vCode
              `unsafeApplyCode` liftCode110 (toBuiltinData ctx)
      resPs = runCekRes vPs

  pure $ case (resHs, resPs) of
    (Left _, Left _) -> property True
    _ -> property False

hsValidatorsAgreesAndPass
  :: (ConstitutionValidator, CompiledCode ConstitutionValidator)
  -> V3.FakeProposedContext
  -> Property
hsValidatorsAgreesAndPass (vHs, vCode) ctx = ioProperty $ do
  resHs <- tryApplyOnData vHs ctx
  let vPs =
        _progTerm $
          getPlcNoAnn $
            vCode
              `unsafeApplyCode` liftCode110 (toBuiltinData ctx)
      resPs = runCekRes vPs

  pure $ case (resHs, resPs) of
    (Right okHs, Right okPs) -> liftCode110Norm okHs === okPs
    _ -> property False
