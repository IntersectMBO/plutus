{-| Measure the overhead of certifier-annotation generation in the UPLC inliner.

The inliner records the certifier annotations ("hints") of each pass lazily in
the optimizer trace, so the cost of building them is only paid when something
demands them. Each measured input is therefore run twice:

* @hints-discarded@ runs the inline pass and forces only the resulting term;
  the trace, and with it the annotation thunks, are dropped unevaluated. This
  is what a non-certifying compilation pays.

* @hints-forced@ runs the inline pass and forces the resulting term /and/ the
  recorded annotations, including the checkpoint terms carried by
  transitive-closure annotations. This is what a certifying compilation pays
  in the inliner.

The relative difference between the two is the annotation-generation overhead.

The inputs are the actual inline instances of each corpus script: the script is
run through the optimizer once, and every term the inliner was given during
that run is recorded. Under the default settings the simplifier runs sixteen
times, so each script contributes sixteen measured inputs, one per inliner run
--- from the first run, which does most of the inlining, to the runs at the
fixpoint, where the inliner rewrites nothing but annotation generation must
still traverse the whole term. This matches the instances measured by
@certifier-inline-table@, whose own tool reports the same overhead; this
standalone benchmark exists to cross-check those figures with full criterion
statistics.

Note that the decoration bookkeeping the inliner performs in order to be able
to produce annotations at all is unconditional, so it is included in both
variants: what is measured here is the marginal cost of materializing them.

Example usage:

> cabal run certifier-overhead-bench -- --time-limit 1 --csv overhead.csv
> python3 plutus-benchmark/certifier/bench-overhead/overhead.py overhead.csv

There are 2 measurements per instance and 16 instances per script, so the run
is long; @--time-limit 1@ keeps it to roughly half an hour. Passing a benchmark
name prefix (e.g. @cabal run certifier-overhead-bench -- coop@) restricts the
run to one script. -}
module Main (main) where

import Certifier.Common (inlineInstances, loadTermFrom, simplify, testScripts)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Criterion.Main
import PlutusCore.Default.Builtins
import PlutusCore.Quote (MonadQuote, runQuote)
import Text.Printf (printf)
import UntypedPlutusCore
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify
import UntypedPlutusCore.Transform.Inline (inline)

type NTerm = Term Name DefaultUni DefaultFun ()

-- | The same options as 'Certifier.Common.simplify' uses for the certifier corpus.
opts :: OptimizeOpts Name ()
opts = defaultOptimizeOpts {_ooPreserveLogging = False}

inlinePass
  :: MonadQuote m
  => NTerm
  -> OptimizerT Name DefaultUni DefaultFun () m NTerm
inlinePass =
  inline
    (_ooInlineUnconditionalGrowth opts)
    (_ooInlineCallsiteGrowth opts)
    (_ooInlineConstants opts)
    (_ooPreserveLogging opts)
    (_ooInlineHints opts)
    DefaultFunSemanticsVariantE

{-| Run the inline pass, forcing only the resulting term. The annotations
recorded in the optimizer trace are dropped unevaluated, as in a
non-certifying compilation. -}
inlineHintsDiscarded :: NTerm -> NTerm
inlineHintsDiscarded = runQuote . evalOptimizerT . inlinePass

{-| Run the inline pass, returning the annotations recorded in the optimizer
trace alongside the resulting term, so that the benchmark ('nf') forces both
(including the checkpoint terms inside the annotations), as in a certifying
compilation. -}
inlineHintsForced :: NTerm -> (NTerm, [Certify.Hints NTerm])
inlineHintsForced t = runQuote $ do
  (t', tr) <- runOptimizerT (inlinePass t)
  pure (t', map hints (optimizerTrace tr))

{-| The terms the inliner was given during one optimizer run of a corpus
script, in the order the inliner ran on them. -}
inlineInputsFor :: FilePath -> IO [NTerm]
inlineInputsFor script = do
  original <- loadTermFrom script
  let (_, tr) = runQuote (simplify original)
  evaluate . force $ map beforeAST (inlineInstances tr)

main :: IO ()
main = do
  corpus <- forM testScripts $ \script -> (,) script <$> inlineInputsFor script
  defaultMain
    [ bgroup
        script
        [ bgroup
            (printf "instance-%02d" i)
            [ bench "hints-discarded" $ nf inlineHintsDiscarded t
            , bench "hints-forced" $ nf inlineHintsForced t
            ]
        | (i, t) <- zip [1 :: Int ..] inputs
        ]
    | (script, inputs) <- corpus
    ]
