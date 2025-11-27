{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Lists.Sum.HandWritten where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import Control.Monad.Except
import Data.Either
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.StdLib.Data.List qualified as BuiltinList
import PlutusCore.StdLib.Data.MatchOption (MatchOption (UseChoose))
import PlutusCore.StdLib.Data.ScottList qualified as ScottList
import PlutusCore.Version qualified as PLC
import PlutusTx qualified as Tx
import PlutusTx.Builtins.Internal qualified as BI
import UntypedPlutusCore qualified as UPLC

---------------- Hand-written folds, using stuff from PlutusCore.StdLib.Data  ----------------

mkBuiltinList :: [Integer] -> Term
mkBuiltinList l = compiledCodeToTerm (Tx.liftCodeDef $ BI.BuiltinList l)

mkSumLeftBuiltinTerm :: [Integer] -> Term
mkSumLeftBuiltinTerm l =
  UPLC.Apply () (debruijnTermUnsafe $ eraseTerm (BuiltinList.sum UseChoose)) (mkBuiltinList l)

mkSumRightBuiltinTerm :: [Integer] -> Term
mkSumRightBuiltinTerm l =
  UPLC.Apply () (debruijnTermUnsafe $ eraseTerm (BuiltinList.sumr UseChoose)) (mkBuiltinList l)

mkScottList :: [Integer] -> Term
mkScottList l = compiledCodeToTerm (Tx.liftCode PLC.plcVersion100 l)

mkSumLeftScottTerm :: [Integer] -> Term
mkSumLeftScottTerm l = UPLC.Apply () (debruijnTermUnsafe $ eraseTerm ScottList.sum) (mkScottList l)

mkSumRightScottTerm :: [Integer] -> Term
mkSumRightScottTerm l =
  UPLC.Apply () (debruijnTermUnsafe $ eraseTerm ScottList.sumr) (mkScottList l)

debruijnTermUnsafe
  :: UPLC.Term UPLC.Name uni fun ann
  -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
debruijnTermUnsafe =
  fromRight (error "debruijnTermUnsafe") . runExcept @UPLC.FreeVariableError . UPLC.deBruijnTerm
