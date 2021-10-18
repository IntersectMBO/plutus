{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Lists.Sum.HandWritten where

import           PlutusBenchmark.Common           (Term, compiledCodeToTerm)

import qualified PlutusCore.StdLib.Data.List      as BuiltinList
import qualified PlutusCore.StdLib.Data.ScottList as ScottList
import qualified PlutusTx                         as Tx
import qualified PlutusTx.Builtins.Internal       as BI
import qualified UntypedPlutusCore                as UPLC


---------------- Hand-written folds, using stuff from PlutusCore.StdLib.Data  ----------------

mkBuiltinList :: [Integer] -> Term
mkBuiltinList l = compiledCodeToTerm (Tx.liftCode $ BI.BuiltinList l)

mkSumLeftBuiltinTerm :: [Integer] -> Term
mkSumLeftBuiltinTerm l = UPLC.Apply () (UPLC.erase BuiltinList.sum) (mkBuiltinList l)

mkSumRightBuiltinTerm :: [Integer] -> Term
mkSumRightBuiltinTerm l = UPLC.Apply () (UPLC.erase BuiltinList.sumr) (mkBuiltinList l)

mkScottList :: [Integer] -> Term
mkScottList l = compiledCodeToTerm (Tx.liftCode l)

mkSumLeftScottTerm :: [Integer] -> Term
mkSumLeftScottTerm l = UPLC.Apply () (UPLC.erase ScottList.sum) (mkScottList l)

mkSumRightScottTerm :: [Integer] -> Term
mkSumRightScottTerm l = UPLC.Apply () (UPLC.erase ScottList.sumr) (mkScottList l)

