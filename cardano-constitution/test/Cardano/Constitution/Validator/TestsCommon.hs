-- editorconfig-checker-disable-file
{-# LANGUAGE TypeOperators #-}

module Cardano.Constitution.Validator.TestsCommon
  ( applyOnData
  , tryApplyOnData
  , allVldtrsErred
  , allVldtrsPassed
  , runCekRes
  , unsafeRunCekRes
  , liftCode110
  , liftCode110Norm
  ) where

import Cardano.Constitution.Validator.Common
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Version (plcVersion110)
import PlutusPrelude
import PlutusTx as Tx
import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal as B
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

import Control.Exception
import Test.Tasty.QuickCheck

applyOnData
  :: ToData ctx
  => ConstitutionValidator
  -> ctx
  -> BuiltinUnit
applyOnData v ctx = v (Tx.toBuiltinData ctx)

-- | Here we try to catch the calls to `Tx.error`.
tryApplyOnData
  :: ToData ctx
  => ConstitutionValidator
  -> ctx
  -> IO (Either ErrorCall BuiltinUnit)
-- TODO: I am not sure that this is enough to test both in Haskell and Tx side, since we may throw
-- other kinds of errors , e.g. `PatternMatchFail` in Haskell-side?
tryApplyOnData v ctx = try $ evaluate $ applyOnData v ctx

allVldtrsErred
  , allVldtrsPassed
    :: ToData ctx
    => [ConstitutionValidator]
    -> ctx
    -> Property

-- | All given validators have to err
allVldtrsErred vs ctx =
  conjoin $
    fmap (\v -> ioProperty (isLeft <$> tryApplyOnData v ctx)) vs

{-| All given validators have to not err

Doing (ioProperty . isRight . tryApplyEval) is probably redundant here, since QC will catch any exceptions -}
allVldtrsPassed vs ctx = conjoin $ fmap (B.fromOpaque . (`applyOnData` ctx)) vs

unsafeRunCekRes
  :: t ~ Term NamedDeBruijn DefaultUni DefaultFun ()
  => t -> t
unsafeRunCekRes = unsafeFromRight . runCekRes

runCekRes
  :: t ~ Term NamedDeBruijn DefaultUni DefaultFun ()
  => t -> Either (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun) t
runCekRes t =
  UPLC.cekResultToEither . UPLC._cekReportResult $
    UPLC.runCekDeBruijn defaultCekParametersForTesting restrictingEnormous noEmitter t

liftCode110 :: Lift DefaultUni a => a -> CompiledCode a
liftCode110 = liftCode plcVersion110

liftCode110Norm :: Lift DefaultUni a => a -> Term NamedDeBruijn DefaultUni DefaultFun ()
liftCode110Norm = unsafeRunCekRes . _progTerm . getPlcNoAnn . liftCode110
