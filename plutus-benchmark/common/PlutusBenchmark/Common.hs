{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

{- | Miscellaneous shared code for benchmarking-related things. -}
module PlutusBenchmark.Common
    ( module Export
    , NamedDeBruijnTerm
    , getConfig
    , compiledCodeToTerm
    , haskellValueToTerm
    , unDeBruijn
    , benchTermCek
    , runTermCek
    , cekResultMatchesHaskellValue
     )
where

import           Paths_plutus_benchmark                   as Export

import qualified PlutusTx                                 as Tx

import qualified PlutusCore                               as PLC
import           PlutusCore.Default
import           PlutusCore.Pretty
import qualified UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import           Control.DeepSeq                          (force)
import           Control.Exception
import           Control.Monad.Trans.Except
import           Criterion.Main
import           Criterion.Types                          (Config (..))
import           Flat
import           System.FilePath

{- | The Criterion configuration returned by `getConfig` will cause an HTML report
   to be generated.  If run via stack/cabal this will be written to the
   `plutus-benchmark` directory by default.  The -o option can be used to change
   this, but an absolute path will probably be required (eg, "-o=$PWD/report.html") . -}
getConfig :: Double -> IO Config
getConfig limit = do
  templateDir <- getDataFileName ("common" </> "templates")
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
  pure $ defaultConfig {
                template = templateFile,
                reportFile = Just "report.html",
                timeLimit = limit
              }

{- | Just extract the body of a program wrapped in a 'CompiledCodeIn'.  We use this a lot. -}
compiledCodeToTerm
    :: ( uni `Everywhere` Flat
       , uni `Everywhere` PrettyConst
       , Closed uni
       , GShow uni
       , Flat fun
       , Pretty fun
       )
      => Tx.CompiledCodeIn uni fun a -> UPLC.Term UPLC.NamedDeBruijn uni fun ()
compiledCodeToTerm x = let (UPLC.Program _ _ body) = Tx.getPlc x in body

{- | Lift a Haskell value to a PLC term.  The constraints get a bit out of control
   if we try to do this over an arbitrary universe.-}
haskellValueToTerm
    :: Tx.Lift DefaultUni a => a -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
haskellValueToTerm = compiledCodeToTerm . Tx.liftCode


type NamedDeBruijnTerm = UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type NamedTerm = UPLC.Term PLC.Name DefaultUni DefaultFun ()

unDeBruijn :: NamedDeBruijnTerm -> NamedTerm
unDeBruijn t =
    case runExcept @PLC.FreeVariableError $ PLC.runQuoteT $ UPLC.unDeBruijnTerm t of
      Left e   -> throw e
      Right t' -> force t'
      -- We're going to be using the results in benchmarks, so let's try to make
      -- sure that the result is fully evaluated to avoid adding the conversion
      -- overhead.

{- | Convert a de-Bruijn-named UPLC term to a Benchmark -}
benchTermCek :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun () -> Benchmarkable
benchTermCek term =
    nf (Cek.unsafeEvaluateCek Cek.noEmitter PLC.defaultCekParameters) $! unDeBruijn term -- Or whnf?

{- | Just run a term (used for tests etc.) -}
runTermCek :: NamedDeBruijnTerm -> EvaluationResult NamedTerm
runTermCek = Cek.unsafeEvaluateCekNoEmit PLC.defaultCekParameters . unDeBruijn


type Result = EvaluationResult NamedTerm

{- | Evaluate a PLC term and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties.  -}
cekResultMatchesHaskellValue :: Tx.Lift DefaultUni a => NamedDeBruijnTerm -> (Result -> Result -> b) -> a -> b
cekResultMatchesHaskellValue term matches value = (runTermCek term) `matches` (runTermCek $ haskellValueToTerm value)
