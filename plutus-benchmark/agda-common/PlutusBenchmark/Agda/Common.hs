{-# LANGUAGE BangPatterns #-}

module PlutusBenchmark.Agda.Common
  ( benchTermAgdaCek
  , benchProgramAgdaCek
  )
where

import PlutusCore qualified as PLC
import PlutusCore.Default (DefaultFun, DefaultUni)
import UntypedPlutusCore qualified as UPLC

import MAlonzo.Code.Evaluator.Term (runUAgda)

import Criterion.Main (Benchmark, bench, nf)

-- This code is in its own file so that we only build the metatheory when we really need it.

type Term = UPLC.Term PLC.NamedDeBruijn DefaultUni DefaultFun ()
type Program = UPLC.Program PLC.NamedDeBruijn DefaultUni DefaultFun ()

---------------- Run a term or program using the plutus-metatheory CEK evaluator ----------------

benchTermAgdaCek :: String -> Term -> Benchmark
benchTermAgdaCek name !term =
    bench name $ nf unsafeRunAgdaCek term

benchProgramAgdaCek :: String -> Program -> Benchmark
benchProgramAgdaCek name (UPLC.Program _ _ !term) =
    bench name $ nf unsafeRunAgdaCek term

unsafeRunAgdaCek :: Term -> PLC.EvaluationResult Term
unsafeRunAgdaCek =
    either (error . \e -> "Agda evaluation error: " ++ show e) PLC.EvaluationSuccess . runUAgda

