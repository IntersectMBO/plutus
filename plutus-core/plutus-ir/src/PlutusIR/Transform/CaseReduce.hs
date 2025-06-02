{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module PlutusIR.Transform.CaseReduce
    ( caseReduce
    , caseReducePass
    ) where

import PlutusCore.Builtin (CaseBuiltin (..))
import PlutusCore.MkPlc
import PlutusIR.Core

import Control.Lens (transformOf, (^?))
import Data.List.Extras
import GHC.IsList (fromList)
import PlutusCore qualified as PLC
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

caseReducePass
  :: ( PLC.Typecheckable uni fun, CaseBuiltin uni
     , PLC.GEq uni, Applicative m
     )
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
caseReducePass tcconfig = simplePass "case reduce" tcconfig caseReduce

caseReduce
    :: CaseBuiltin uni
    => Term tyname name uni fun a -> Term tyname name uni fun a
caseReduce = transformOf termSubterms processTerm

processTerm
    :: CaseBuiltin uni
    => Term tyname name uni fun a -> Term tyname name uni fun a
processTerm = \case
    Case ann _ (Constr _ _ i args) cs | Just c <- cs ^? wix i -> mkIterApp c ((ann,) <$> args)
    Case ann resTy (Constant _ con) cs -> case caseBuiltin con $ fromList cs of
        Left _    -> Error ann resTy
        Right res -> res
    t -> t
