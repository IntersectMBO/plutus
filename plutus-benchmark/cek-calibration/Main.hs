{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

{- | Benchmarks for some simple functions operating on lists.  These are used to
get an idea of the average cost of the basic CEK operations.
-}
-- TODO: these are currently run manually, but the process should be automated.

-- See Note [Creation of the Cost Model]
module Main (main) where


import Prelude qualified as Haskell

import PlutusCore
import PlutusCore.Pretty qualified as PP
import PlutusTx qualified as Tx
import PlutusTx.Prelude as Tx
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Exception
import Control.Lens
import Control.Monad.Except
import Criterion.Main
import Criterion.Types qualified as C

type PlainTerm = UPLC.Term Name DefaultUni DefaultFun ()


benchCek :: UPLC.Term NamedDeBruijn DefaultUni DefaultFun () -> Benchmarkable
benchCek t = case runExcept @UPLC.FreeVariableError $ runQuoteT $ UPLC.unDeBruijnTerm t of
    Left e   -> throw e
    Right t' -> whnf (unsafeEvaluateCekNoEmit defaultCekParameters) t'


{-# INLINABLE rev #-}
rev :: [()] -> [()]
rev l0 = rev' l0 []
    where rev' l acc =
              case l of
                []   -> acc
                x:xs -> rev' xs (x:acc)

{-# INLINABLE mkList #-}
mkList :: Integer -> [()]
mkList m = mkList' m []
    where mkList' n acc =
              if n == 0 then acc
              else mkList' (n-1) (():acc)

{-# INLINABLE zipl #-}
zipl :: [()] -> [()] -> [()]
zipl [] []         = []
zipl l []          = l
zipl [] l          = l
zipl (x:xs) (y:ys) = x:y:(zipl xs ys)

{-# INLINABLE go #-}
go :: Integer -> [()]
go n = zipl (mkList n) (rev $ mkList n)


mkListProg :: Integer -> UPLC.Program NamedDeBruijn DefaultUni DefaultFun ()
mkListProg n = Tx.getPlc $ $$(Tx.compile [|| go ||]) `Tx.applyCode` Tx.liftCode n

mkListTerm :: Integer -> UPLC.Term NamedDeBruijn DefaultUni DefaultFun ()
mkListTerm n =
  let (UPLC.Program _ _ code) = mkListProg n
  in code

mkListBM :: Integer -> Benchmark
mkListBM n = bench (Haskell.show n) $ benchCek (mkListTerm n)

mkListBMs :: [Integer] -> Benchmark
mkListBMs ns = bgroup "List" [mkListBM n | n <- ns]

writePlc :: UPLC.Program NamedDeBruijn DefaultUni DefaultFun () -> Haskell.IO ()
writePlc p =
    case runExcept @UPLC.FreeVariableError $ runQuoteT $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm p of
      Left e   -> throw e
      Right p' -> Haskell.print . PP.prettyPlcClassicDebug $ p'


main1 :: Haskell.IO ()
main1 = defaultMainWith (defaultConfig { C.csvFile = Just "cek-lists.csv" }) $ [mkListBMs [0,10..1000]]

main2:: Haskell.IO ()
main2 = writePlc (mkListProg 999)

main :: Haskell.IO ()
main = main1
