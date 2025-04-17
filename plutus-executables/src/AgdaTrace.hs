module AgdaTrace (
    mkAgdaTrace,
) where

import Untyped qualified as AgdaFFI

import PlutusPrelude

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

mkAgdaTrace
  :: SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> [(SimplifierStage, (AgdaFFI.UTerm, AgdaFFI.UTerm))]
mkAgdaTrace (SimplifierTrace simplTrace) = reverse $ processAgdaAST <$> simplTrace
  where
    processAgdaAST Simplification {beforeAST, stage, afterAST} =
              case (UPLC.deBruijnTerm beforeAST, UPLC.deBruijnTerm afterAST) of
                (Right before', Right after')             ->
                  (stage, (AgdaFFI.conv (void before'), AgdaFFI.conv (void after')))
                (Left (err :: UPLC.FreeVariableError), _) -> error $ show err
                (_, Left (err :: UPLC.FreeVariableError)) -> error $ show err
