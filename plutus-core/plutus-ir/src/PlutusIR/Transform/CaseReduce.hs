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
import Data.Bifunctor (second)
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
    -- We could've rewritten those patterns as 'Error' in the 'Nothing' cases, but that would turn a
    -- structural error into an operational one, which would be unfortunate, so instead we decided
    -- not to fully optimize such scripts, since they aren't valid anyway.
    Case ann _ (Constr _ _ i args) cs | Just c <- cs ^? wix i -> mkIterApp c ((ann,) <$> args)
    Case ann _ (Constant _ con) cs
      | Right t <- headSpineToTerm ann (second (Constant ann) (caseBuiltin con (fromList cs))) -> t

    t -> t
