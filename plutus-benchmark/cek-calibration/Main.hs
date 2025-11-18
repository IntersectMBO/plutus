{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- TODO: these are currently run manually, but the process should be automated.

-- See plutus-core/cost-model/CostModelGeneration.hs

{-| Benchmarks for some simple functions operating on lists.  These are used to
get an idea of the average cost of the basic CEK operations. -}
module Main (main) where

import Prelude qualified as Haskell

import PlutusBenchmark.Common (benchTermCek, mkMostRecentEvalCtx)
import PlutusCore
import PlutusCore.Pretty qualified as PP
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusTx qualified as Tx
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx
import UntypedPlutusCore as UPLC

import Control.Exception
import Control.Lens
import Control.Monad.Except
import Criterion.Main
import Criterion.Types qualified as C

type PlainTerm = UPLC.Term Name DefaultUni DefaultFun ()

rev :: [()] -> [()]
rev l0 = rev' l0 []
  where
    rev' l acc =
      case l of
        [] -> acc
        x : xs -> rev' xs (x : acc)
{-# INLINEABLE rev #-}

mkList :: Integer -> [()]
mkList m = mkList' m []
  where
    mkList' n acc =
      if n == 0
        then acc
        else mkList' (n - 1) (() : acc)
{-# INLINEABLE mkList #-}

zipl :: [()] -> [()] -> [()]
zipl [] [] = []
zipl l [] = l
zipl [] l = l
zipl (x : xs) (y : ys) = x : y : (zipl xs ys)
{-# INLINEABLE zipl #-}

go :: Integer -> [()]
go n = zipl (mkList n) (rev $ mkList n)
{-# INLINEABLE go #-}

mkListProg :: Integer -> UPLC.Program NamedDeBruijn DefaultUni DefaultFun ()
mkListProg n = Tx.getPlcNoAnn $ $$(Tx.compile [||go||]) `Tx.unsafeApplyCode` Tx.liftCodeDef n

mkListTerm :: Integer -> UPLC.Term NamedDeBruijn DefaultUni DefaultFun ()
mkListTerm n =
  let (UPLC.Program _ _ code) = mkListProg n
   in code

mkListBM :: EvaluationContext -> Integer -> Benchmark
mkListBM ctx n = bench (Haskell.show n) $ benchTermCek ctx (mkListTerm n)

mkListBMs :: EvaluationContext -> [Integer] -> Benchmark
mkListBMs ctx ns = bgroup "List" [mkListBM ctx n | n <- ns]

writePlc :: UPLC.Program NamedDeBruijn DefaultUni DefaultFun () -> Haskell.IO ()
writePlc p =
  case runExcept @UPLC.FreeVariableError
    $ runQuoteT
    $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm p of
    Left e -> throw e
    Right p' -> Haskell.print . PP.prettyPlcClassicSimple $ p'

main1 :: Haskell.IO ()
main1 = do
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith
    (defaultConfig {C.csvFile = Just "cek-lists.csv"})
    [mkListBMs evalCtx [0, 10 .. 1000]]

main2 :: Haskell.IO ()
main2 = writePlc (mkListProg 999)

main :: Haskell.IO ()
main = main1
