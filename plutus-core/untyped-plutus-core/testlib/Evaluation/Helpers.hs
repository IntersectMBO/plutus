-- editorconfig-checker-disable-file
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

-- | Various helpers for defining evaluation tests.
module Evaluation.Helpers
  ( -- * Generators
    forAllByteString
  , forAllByteStringThat

    -- * Evaluation helpers
  , evaluateTheSame
  , evaluatesToConstant
  , assertEvaluatesToConstant
  , evaluateToHaskell
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Evaluation.Builtins.Common (typecheckEvaluateCek, typecheckReadKnownCek)
import GHC.Stack (HasCallStack)
import Hedgehog (PropertyT, annotateShow, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric (showHex)
import PlutusCore qualified as PLC
import PlutusCore.Builtin (ReadKnownIn)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting)
import PlutusCore.MkPlc (mkConstant)
import PlutusPrelude (Word8, def)
import Test.Tasty.HUnit (assertEqual, assertFailure)
import UntypedPlutusCore qualified as UPLC

{-| Given a lower and upper bound (both inclusive) on length, generate a 'ByteString' whose length
falls within these bounds. Furthermore, the generated 'ByteString' will show as a list of
hex-encoded bytes on a failure, instead of the default 'Show' output.

= Note

It is the caller's responsibility to ensure that the bounds are sensible: that is, that neither
the upper or lower bound are negative, and that the lower bound is not greater than the upper
bound. -}
forAllByteString
  :: forall (m :: Type -> Type)
   . (Monad m, HasCallStack)
  => Int -> Int -> PropertyT m ByteString
forAllByteString lo = forAllWith hexShow . Gen.bytes . Range.linear lo

{-| As 'forAllByteString', but with a postcondition.

= Note

If the postcondition is unlikely, the generator may eventually fail after too many retries.
Ensure that the postcondition is likely to avoid problems. -}
forAllByteStringThat
  :: forall (m :: Type -> Type)
   . (Monad m, HasCallStack)
  => (ByteString -> Bool) -> Int -> Int -> PropertyT m ByteString
forAllByteStringThat p lo = forAllWith hexShow . Gen.filterT p . Gen.bytes . Range.linear lo

{-| Typechecks and evaluates both PLC expressions. If either of them fail to typecheck, fail the
test, noting what the failure was. If both typecheck, but either errors when run, fail the test,
noting the log(s) for any failing expression. If both run without error, compare the results
using '==='. -}
evaluateTheSame
  :: HasCallStack
  => PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PropertyT IO ()
evaluateTheSame lhs rhs =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting lhs of
    Left x -> annotateShow x >> failure
    Right (resLhs, logsLhs) -> case typecheckEvaluateCek def defaultBuiltinCostModelForTesting rhs of
      Left x -> annotateShow x >> failure
      Right (resRhs, logsRhs) -> case (resLhs, resRhs) of
        (PLC.EvaluationFailure, PLC.EvaluationFailure) -> do
          annotateShow logsLhs
          annotateShow logsRhs
          failure
        (PLC.EvaluationSuccess rLhs, PLC.EvaluationSuccess rRhs) -> rLhs === rRhs
        (PLC.EvaluationFailure, _) -> annotateShow logsLhs >> failure
        (_, PLC.EvaluationFailure) -> annotateShow logsRhs >> failure

{-| As 'evaluateTheSame', but for cases where we want to compare a more complex computation to a
constant (as if by @mkConstant@). This is slightly more efficient. -}
evaluatesToConstant
  :: forall (a :: Type)
   . PLC.Contains UPLC.DefaultUni a
  => a
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PropertyT IO ()
evaluatesToConstant k expr =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting expr of
    Left err -> annotateShow err >> failure
    Right (res, logs) -> case res of
      PLC.EvaluationFailure -> annotateShow logs >> failure
      PLC.EvaluationSuccess r -> r === mkConstant () k

{-| Given a PLC expression and an intended type (via a type argument), typecheck the expression,
evaluate it, then produce the required Haskell value from the results. If we fail at any stage,
instead fail the test and report the failure. -}
evaluateToHaskell
  :: forall (a :: Type)
   . ReadKnownIn UPLC.DefaultUni (UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()) a
  => PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> PropertyT IO a
evaluateToHaskell expr =
  case typecheckReadKnownCek def defaultBuiltinCostModelForTesting expr of
    Left err -> annotateShow err >> failure
    Right (Left err) -> annotateShow err >> failure
    Right (Right x) -> pure x

-- | As 'evaluatesToConstant', but for a unit instead of a property.
assertEvaluatesToConstant
  :: forall (a :: Type)
   . PLC.Contains UPLC.DefaultUni a
  => a
  -> PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -> IO ()
assertEvaluatesToConstant k expr =
  case typecheckEvaluateCek def defaultBuiltinCostModelForTesting expr of
    Left err -> assertFailure . show $ err
    Right (res, logs) -> case res of
      PLC.EvaluationFailure -> assertFailure . show $ logs
      PLC.EvaluationSuccess r -> assertEqual "" r (mkConstant () k)

-- Helpers

hexShow :: ByteString -> String
hexShow bs = "[" <> (go . BS.unpack $ bs) <> "]"
  where
    go :: [Word8] -> String
    go = \case
      [] -> ""
      [w8] -> byteToHex w8
      (w8 : w8s) -> byteToHex w8 <> ", " <> go w8s

byteToHex :: Word8 -> String
byteToHex w8
  | w8 < 128 = "0x0" <> showHex w8 ""
  | otherwise = "0x" <> showHex w8 ""
