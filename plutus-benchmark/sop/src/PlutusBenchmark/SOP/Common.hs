{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns  #-}

module PlutusBenchmark.SOP.Common where

import Data.Functor
import PlutusCore.Annotation
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Version (plcVersion110)
import PlutusTx
import PlutusTx.Code
import Prelude
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

unsafeRunCekRes
  :: Term NamedDeBruijn DefaultUni DefaultFun ()
  -> Term NamedDeBruijn DefaultUni DefaultFun SrcSpans
unsafeRunCekRes x =
  case runCekRes x of
    Right x' -> x' $> mempty
    Left _   -> error "no"

runCekRes
  :: Term NamedDeBruijn DefaultUni DefaultFun ()
  -> Either
       (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
       (Term NamedDeBruijn DefaultUni DefaultFun ())
runCekRes t =
    UPLC.cekResultToEither . UPLC._cekReportResult $
    UPLC.runCekDeBruijn defaultCekParametersForTesting restrictingEnormous noEmitter t

liftCode110 :: Lift DefaultUni a => a -> CompiledCode a
liftCode110 = liftCode plcVersion110

liftCode110Norm :: Lift DefaultUni a => a -> CompiledCode a
liftCode110Norm x =
  DeserializedCode
    (Program mempty plcVersion110 (unsafeRunCekRes $ _progTerm $ getPlcNoAnn $ liftCode110 $ x))
    Nothing
    mempty

normCompiledCode :: CompiledCode a -> CompiledCode a
normCompiledCode code =
  let
    UPLC.Program _ v term = getPlcNoAnn code
  in DeserializedCode
       (Program mempty v (unsafeRunCekRes term))
       Nothing
       mempty

app :: CompiledCode (a -> b) -> CompiledCode a -> CompiledCode b
app f x =
  case UPLC.applyProgram (getPlc f) (getPlc x) of
    Right res -> DeserializedCode res Nothing mempty
    Left _    -> error "no"
