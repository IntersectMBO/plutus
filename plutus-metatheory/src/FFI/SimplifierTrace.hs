{-# OPTIONS_GHC -Wall #-}

module FFI.SimplifierTrace
  ( TraceElem
  , Trace
  , mkFfiSimplifierTrace
  ) where

import FFI.Untyped qualified as FFI

import PlutusPrelude

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify
import UntypedPlutusCore.Transform.Simplifier

type TraceElem a = (SimplifierStage, (Certify.Hints, (a, a)))
type Trace a = [TraceElem a]

mkFfiSimplifierTrace
  :: SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> Trace FFI.UTerm
mkFfiSimplifierTrace (SimplifierTrace simplTrace) = reverse $ toFfiAst <$> simplTrace
  where
    toFfiAst (Simplification before stage hints after) =
      case (UPLC.deBruijnTerm before, UPLC.deBruijnTerm after) of
        (Right before', Right after') ->
          (stage, (hints, (FFI.conv (void before'), FFI.conv (void after'))))
        (Left (err :: UPLC.FreeVariableError), _) -> error $ show err
        (_, Left (err :: UPLC.FreeVariableError)) -> error $ show err
