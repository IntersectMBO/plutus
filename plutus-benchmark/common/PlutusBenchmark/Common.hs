{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Miscellaneous shared code for benchmarking-related things. -}
module PlutusBenchmark.Common
    ( module Export
    , Term
    , getConfig
    , toAnonDeBruijnTerm
    , toNamedDeBruijnTerm
    , compiledCodeToTerm
    , haskellValueToTerm
    , benchTermCek
    , runTermCek
    , cekResultMatchesHaskellValue
     )
where

import Paths_plutus_benchmark as Export

import PlutusTx qualified as Tx

import PlutusCore qualified as PLC
import PlutusCore.Default
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import Criterion.Main
import Criterion.Types (Config (..))
import System.FilePath

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

type Term    = UPLC.Term PLC.NamedDeBruijn DefaultUni DefaultFun ()

{- | Given a DeBruijn-named term, give every variable the name "v".  If we later
   call unDeBruijn, that will rename the variables to things like "v123", where
   123 is the relevant de Bruijn index.-}
toNamedDeBruijnTerm
    :: UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
    -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
toNamedDeBruijnTerm = UPLC.termMapNames UPLC.fakeNameDeBruijn

{- | Remove the textual names from a NamedDeBruijn term -}
toAnonDeBruijnTerm
    :: Term
    -> UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
toAnonDeBruijnTerm = UPLC.termMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix)

{- | Just extract the body of a program wrapped in a 'CompiledCodeIn'.  We use this a lot. -}
compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> Term
compiledCodeToTerm (Tx.getPlc -> UPLC.Program _ _ body) = body

{- | Lift a Haskell value to a PLC term.  The constraints get a bit out of control
   if we try to do this over an arbitrary universe.-}
haskellValueToTerm
    :: Tx.Lift DefaultUni a => a -> Term
haskellValueToTerm = compiledCodeToTerm . Tx.liftCode


{- | Convert a de-Bruijn-named UPLC term to a Benchmark -}
benchTermCek :: Term -> Benchmarkable
benchTermCek term =
    nf (runTermCek) $! term -- Or whnf?

{- | Just run a term (used for tests etc.) -}
runTermCek :: Term -> EvaluationResult Term
runTermCek = unsafeExtractEvaluationResult . (\ (fstT,_,_) -> fstT) . runCekDeBruijn PLC.defaultCekParameters Cek.restrictingEnormous Cek.noEmitter

type Result = EvaluationResult Term

{- | Evaluate a PLC term and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties.  -}
cekResultMatchesHaskellValue :: Tx.Lift DefaultUni a => Term -> (Result -> Result -> b) -> a -> b
cekResultMatchesHaskellValue term matches value = (runTermCek term) `matches` (runTermCek $ haskellValueToTerm value)
