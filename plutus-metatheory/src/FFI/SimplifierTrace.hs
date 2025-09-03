{-# OPTIONS_GHC -Wall #-}

module FFI.SimplifierTrace (
    mkFfiSimplifierTrace,
) where

import FFI.Untyped qualified as FFI

import PlutusPrelude

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

mkFfiSimplifierTrace
  :: SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> [(SimplifierStage, (FFI.UTerm, FFI.UTerm))]
mkFfiSimplifierTrace (SimplifierTrace simplTrace) = reverse $ toFfiAst <$> simplTrace
  where
    toFfiAst Simplification {beforeAST, stage, afterAST} =
      case (UPLC.deBruijnTerm beforeAST, UPLC.deBruijnTerm afterAST) of
        (Right before', Right after')             ->
          (stage, (FFI.conv (void before'), FFI.conv (void after')))
        (Left (err :: UPLC.FreeVariableError), _) -> error $ show err
        (_, Left (err :: UPLC.FreeVariableError)) -> error $ show err
