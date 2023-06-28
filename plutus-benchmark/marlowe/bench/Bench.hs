{- | Plutus benchmarks based on some Marlowe examples. -}
module Main where

import Criterion.Main

import Language.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import Language.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusBenchmark.Common (benchTermCek, compiledCodeToTerm, getConfig)

benchPayout :: Benchmarkable
benchPayout = benchTermCek $ compiledCodeToTerm rolePayoutValidator

benchSemantics :: Benchmarkable
benchSemantics = benchTermCek $ compiledCodeToTerm marloweValidator

main :: IO ()
main = do
  -- Run each benchmark for at least one minute.  Change this with -L or --timeout.
  config <- getConfig 60.0
  defaultMainWith config [
    bench "role payout" benchPayout
    , bench "semantics" benchSemantics]
