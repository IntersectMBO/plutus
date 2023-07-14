{-# LANGUAGE RecordWildCards #-}

{- | Plutus benchmarks based on some Marlowe examples. -}

module Main where
import Criterion.Main (Benchmark, Benchmarkable, bench, bgroup, defaultMainWith)

import PlutusBenchmark.Common (benchTermCek, getConfig)
import PlutusBenchmark.Marlowe.BenchUtil (rolePayoutBenchmarks, semanticsBenchmarks)
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidator)
import PlutusBenchmark.Marlowe.Scripts.Semantics (marloweValidator)
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusCore.DeBruijn.Internal (NamedDeBruijn)
import PlutusCore.Default qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Name qualified as PLC
import PlutusLedgerApi.V2 (scriptContextTxInfo, toData, txInfoId)
import PlutusPrelude (void, (.*))
import PlutusTx.Code (CompiledCode, getPlc)
import UntypedPlutusCore (applyProgram)
import UntypedPlutusCore.Core.Type qualified as UPLC
type UplcProg = UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun ()

-- | Turn a `PlutusBenchmark.Marlowe.Types.Benchmark` to a UPLC program.
benchmarkToUPLC
  :: CompiledCode a
  -- ^ semantics or role payout validator.
  -> M.Benchmark
  -- ^ `PlutusBenchmark.Marlowe.Types.Benchmark`, benchmarking type used by the executable,
  -- it includes benchmarking results along with script info.
  -> UPLC.Term NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
  -- A named DeBruijn term, for turning to `Benchmarkable`.
benchmarkToUPLC validator M.Benchmark{..} =
  let
    unsafeFromRight (Right x) = x
    unsafeFromRight _         = error "unsafeFromRight: applyProgram returned a Left"
    wrap = UPLC.Program () (UPLC.Version 1 0 0)
    datum = wrap $ mkConstant () bDatum
    redeemer = wrap $ mkConstant () bRedeemer
    context = wrap $ mkConstant () $ toData bScriptContext
    prog = getPlc validator
    appliedProg = foldl1 (unsafeFromRight .* applyProgram)
        $ void prog : [datum, redeemer, context]
  in
    UPLC._progTerm appliedProg

mkBenchmarkable :: CompiledCode a -> M.Benchmark -> (String, Benchmarkable)
mkBenchmarkable validator bm@M.Benchmark{..} =
  let benchName = show $ txInfoId $ scriptContextTxInfo bScriptContext
  in
    (benchName, benchTermCek $ benchmarkToUPLC validator bm )

main :: IO ()
main = do

  -- Read the semantics benchmark files.
  semanticsMBench <- either error id <$> semanticsBenchmarks

  -- Read the role payout benchmark files.
  rolePayoutMBench <- either error id <$> rolePayoutBenchmarks

  let
    uncurriedBench :: (String, Benchmarkable) -> Benchmark
    uncurriedBench = uncurry bench
    semanticsBench :: [Benchmark] -- list of criterion semantics Benchmarks
    semanticsBench =
      fmap (uncurriedBench . mkBenchmarkable marloweValidator) semanticsMBench
    rolePayoutBench :: [Benchmark] -- list of criterion role payout Benchmarks
    rolePayoutBench =
      fmap (uncurriedBench . mkBenchmarkable rolePayoutValidator) rolePayoutMBench

  -- Run each benchmark for 5 secs by default. This benchmark runs on the longitudinal
  -- benchmarking flow so we don't want to set it higher by default. One can change this with -L or
  -- --timeout when running locally.
  config <- getConfig 5.0
  defaultMainWith config [
    bgroup "semantics" semanticsBench
    , bgroup "role payout" rolePayoutBench]
