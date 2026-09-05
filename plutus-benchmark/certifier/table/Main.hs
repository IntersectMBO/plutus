{-| Generate the measurements for the certifier paper's evaluation table:
for each corpus script, the total sizes of the terms entering and leaving the
inline pass, the total size of the annotations ("certifier hints") the inliner
emitted, the time to certify the inline instances with the Agda-extracted
certifier, the time the inliner itself takes on the same inputs, and the
overhead that emitting annotations adds to the inliner.

For each inline instance (one per simplifier run) the tool

* extracts the (pre-term, annotations, post-term) triple recorded in the
  optimizer trace,

* certifies it in isolation, by wrapping the triple in a single-step trace
  and calling 'runCertifierMain'. Note that, besides running the checker,
  this includes the certifier's scope checking of the terms (conversion to
  intrinsically scoped syntax), but none of the other passes;

* re-runs the inliner on the recorded pre-term with the annotations left
  unforced, as in a non-certifying compilation; and

* re-runs the inliner with the annotations forced (including the checkpoint
  terms they carry), as in a certifying compilation. The relative difference
  with the previous measurement is the annotation-generation overhead.

Each quantity is timed with criterion-measurement: after a warm-up run that
also calibrates the batch size, it is measured over BATCHES batches of
roughly BUDGET_SECS each, and the minimum per-iteration time across batches
is reported.

Annotation sizes count the constructors of the annotation, including the AST
nodes of the checkpoint terms carried by transitive-closure annotations.

Outputs:

* a human-readable table on stdout,

* @inline-table.tex@, the paper's table,

* @inline-table.csv@, one row per script, including the per-script overhead
  range, and

* @inline-instances.csv@, one row per inline instance, including the
  per-instance term, annotation and checkpoint counts (for scaling plots).

Usage:

> cabal run certifier-inline-table -- [BUDGET_SECS] [BATCHES]

where BUDGET_SECS is the target measurement time per batch (default 1.0)
and BATCHES is the number of measurement batches (default 3). -}
module Main (main) where

import Certifier.Common (inlineInstances, loadTermFrom, simplify, testScripts)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Criterion.Measurement (initializeTime, measure)
import Criterion.Measurement.Types (Benchmarkable, Measured (..), nf, whnf)
import Data.Int (Int64)
import Data.List (intercalate, isSuffixOf)
import FFI.OptimizerTrace (Trace, mkFfiOptimizerTrace)
import FFI.Untyped (UTerm)
import MAlonzo.Code.Certifier (runCertifierMain)
import PlutusCore.Default.Builtins
import PlutusCore.Quote (MonadQuote, runQuote)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)
import UntypedPlutusCore
import UntypedPlutusCore.Transform.Certify.Hints qualified as CH
import UntypedPlutusCore.Transform.Inline (inline)

type NTerm = Term Name DefaultUni DefaultFun ()

{-| The same options as 'Certifier.Common.simplify' uses for the certifier
corpus. -}
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

{-| Run the inline pass, forcing only the resulting term; the annotations
recorded in the optimizer trace are dropped unevaluated, as in a
non-certifying compilation. -}
runInliner :: NTerm -> NTerm
runInliner = runQuote . evalOptimizerT . inlinePass

{-| Run the inline pass, returning the annotations recorded in the optimizer
trace alongside the resulting term, so that the benchmark ('nf') forces
both (including the checkpoint terms inside the annotations), as in a
certifying compilation. -}
runInlinerForcingHints :: NTerm -> (NTerm, [CH.Hints NTerm])
runInlinerForcingHints t = runQuote $ do
  (t', tr) <- runOptimizerT (inlinePass t)
  pure (t', map hints (optimizerTrace tr))

{-| Certify a single-step trace, forcing only the verdict (the lazily built
report string is not demanded). -}
certifyBool :: Trace UTerm -> Bool
certifyBool t = case runCertifierMain t [] of
  Just (b, _) -> b
  Nothing -> error "certifier-inline-table: ill-scoped or empty trace"

-- | The number of constructors in a single-step inline annotation.
hintNodeCount :: CH.Inline -> Integer
hintNodeCount CH.InlVar = 1
hintNodeCount (CH.InlLam h) = 1 + hintNodeCount h
hintNodeCount (CH.InlApply f a) = 1 + hintNodeCount f + hintNodeCount a
hintNodeCount (CH.InlForce h) = 1 + hintNodeCount h
hintNodeCount (CH.InlDelay h) = 1 + hintNodeCount h
hintNodeCount CH.InlCon = 1
hintNodeCount CH.InlBuiltin = 1
hintNodeCount CH.InlError = 1
hintNodeCount (CH.InlConstr hs) = 1 + sum (map hintNodeCount hs)
hintNodeCount (CH.InlCase h hs) = 1 + hintNodeCount h + sum (map hintNodeCount hs)
hintNodeCount (CH.InlExpand h) = 1 + hintNodeCount h
hintNodeCount (CH.InlDrop h) = 1 + hintNodeCount h

{-| The size of an annotation, counting the AST nodes of the checkpoint
terms carried by transitive-closure annotations. -}
annSize :: CH.Hints NTerm -> Integer
annSize (CH.Inline s) = go s
  where
    go (CH.InlOne h) = hintNodeCount h
    go (CH.InlSeq l t r) = 1 + go l + termSize t + go r
annSize CH.NoHints = 0

-- | The number of checkpoint terms carried by an annotation.
checkpointCount :: CH.Hints NTerm -> Int
checkpointCount (CH.Inline s) = go s
  where
    go (CH.InlOne _) = 0
    go (CH.InlSeq l _ r) = 1 + go l + go r
checkpointCount CH.NoHints = 0

termSize :: NTerm -> Integer
termSize = unAstSize . termAstSize

{-| Time a 'Benchmarkable': one warm-up/calibration run, then @batches@
batches sized to roughly @budget@ seconds each; report the minimum
per-iteration time across the batches. -}
timeBench :: Double -> Int -> Benchmarkable -> IO Double
timeBench budget batches bm = do
  (m0, _) <- measure bm 1
  let t1 = max (measTime m0) 1e-9
      iters :: Int64
      iters = max 1 (min 1000 (floor (budget / t1)))
  ms <- forM [1 .. batches] $ \_ -> fst <$> measure bm iters
  pure (minimum [measTime m / fromIntegral (measIters m) | m <- ms])

data InstanceRow = InstanceRow
  { irIndex :: Int
  , irPreSize :: Integer
  , irPostSize :: Integer
  , irAnnSize :: Integer
  , irCheckpoints :: Int
  , irCertified :: Bool
  , irCertifyTime :: Double
  , irInlineTime :: Double
  , irInlineForcedTime :: Double
  }

data ScriptRow = ScriptRow
  { srScript :: String
  , srPreSize :: Integer
  , srPostSize :: Integer
  , srAnnSize :: Integer
  , srInstances :: Int
  , srCertifyTime :: Double
  , srInlineTime :: Double
  , srOverhead :: Double -- cost-weighted overhead: total forced / total inline
  , srOverheadGeo :: Double -- geometric mean of the per-instance ratios
  , srOverheadLo :: Double
  , srOverheadHi :: Double
  , srAllCertified :: Bool
  }

geomean :: [Double] -> Double
geomean [] = 1
geomean xs = exp (sum (map log xs) / fromIntegral (length xs))

processScript :: Double -> Int -> FilePath -> IO (ScriptRow, [InstanceRow])
processScript budget batches script = do
  hPutStrLn stderr $ "== " <> script
  original <- evaluate . force =<< loadTermFrom script
  let (finalTerm, tr) = runQuote (simplify original)
      inlineSteps = inlineInstances tr
  _ <- evaluate (force finalTerm)
  rows <- forM (zip [1 ..] inlineSteps) $ \(i, Optimization pre _ hs post) -> do
    _ <- evaluate (force pre)
    _ <- evaluate (force post)
    theAnnSize <- evaluate . force $ annSize hs
    ffiTrace <-
      evaluate . force $
        mkFfiOptimizerTrace (OptimizerTrace [Optimization pre InlineStage hs post])
    let certified = certifyBool ffiTrace
    certifyTime <- timeBench budget batches (whnf certifyBool ffiTrace)
    inlineTime <- timeBench budget batches (nf runInliner pre)
    inlineForcedTime <- timeBench budget batches (nf runInlinerForcingHints pre)
    hPutStrLn stderr $
      printf
        "   inline #%02d: pre=%7d post=%7d ann=%7d ckpts=%2d certified=%-5s certify=%.6fs inline=%.6fs overhead=%.1f%%"
        i
        (termSize pre)
        (termSize post)
        theAnnSize
        (checkpointCount hs)
        (show certified)
        certifyTime
        inlineTime
        ((inlineForcedTime / inlineTime - 1) * 100)
    pure
      InstanceRow
        { irIndex = i
        , irPreSize = termSize pre
        , irPostSize = termSize post
        , irAnnSize = theAnnSize
        , irCheckpoints = checkpointCount hs
        , irCertified = certified
        , irCertifyTime = certifyTime
        , irInlineTime = inlineTime
        , irInlineForcedTime = inlineForcedTime
        }
  let ratios = [irInlineForcedTime r / irInlineTime r | r <- rows]
      totalInlineForced = sum (map irInlineForcedTime rows)
      totalInline = sum (map irInlineTime rows)
  pure
    ( ScriptRow
        { srScript = script
        , srPreSize = sum (map irPreSize rows)
        , srPostSize = sum (map irPostSize rows)
        , srAnnSize = sum (map irAnnSize rows)
        , srInstances = length rows
        , srCertifyTime = sum (map irCertifyTime rows)
        , srInlineTime = totalInline
        , -- The headline overhead is cost-weighted (total forced time over
          -- total discarded time), so it is not diluted by the many fixpoint
          -- rounds that do no annotation work. The per-instance geometric mean
          -- and range are kept in the CSV; the range is dominated by
          -- measurement noise on the cheap rounds (where the true overhead is
          -- ~0, so its sign is random) and is not meant for the paper.
          srOverhead = totalInlineForced / totalInline
        , srOverheadGeo = geomean ratios
        , srOverheadLo = if null ratios then 1 else minimum ratios
        , srOverheadHi = if null ratios then 1 else maximum ratios
        , srAllCertified = all irCertified rows
        }
    , rows
    )

dropUplc :: String -> String
dropUplc s
  | ".uplc" `isSuffixOf` s = take (length s - 5) s
  | otherwise = s

pct :: Double -> Double
pct ratio = (ratio - 1) * 100

-- | A percentage for LaTeX output, with a proper minus sign.
texPct :: Double -> String
texPct ratio
  | p < 0 = printf "$-$%.1f\\%%" (abs p)
  | otherwise = printf "%.1f\\%%" p
  where
    p = pct ratio

texTable :: [ScriptRow] -> String
texTable rows =
  unlines $
    [ "\\begin{table*}"
    , "\\caption{Measuring the UPLC Inliner and Certifier on 12 Programs}"
    , "\\label{tab:inline-eval}"
    , "\\centering"
    , "\\small"
    , "\\begin{tabular}{@{}lrrrrrrr@{}}"
    , "\\toprule"
    , "script & pre & post & ann & inline (s) & certify (s) & certify / inline & ann overhead \\\\"
    , "\\midrule"
    ]
      ++ map texRow rows
      ++ [ "\\bottomrule"
         , "\\end{tabular}"
         , "\\end{table*}"
         ]
  where
    texRow r =
      printf
        "%-23s & %6d & %6d & %6d & %.3f & %.3f & %.0f\\%% & %s \\\\"
        (dropUplc (srScript r))
        (srPreSize r)
        (srPostSize r)
        (srAnnSize r)
        (srInlineTime r)
        (srCertifyTime r)
        (srCertifyTime r / srInlineTime r * 100)
        (texPct (srOverhead r))

scriptCsvHeader :: String
scriptCsvHeader =
  "script,pre_size,post_size,ann_size,inline_instances,inline_time_s,\
  \certify_time_s,ann_overhead,ann_overhead_geomean,ann_overhead_min,\
  \ann_overhead_max,all_certified"

scriptCsvRow :: ScriptRow -> String
scriptCsvRow r =
  intercalate
    ","
    [ srScript r
    , show (srPreSize r)
    , show (srPostSize r)
    , show (srAnnSize r)
    , show (srInstances r)
    , printf "%.6f" (srInlineTime r)
    , printf "%.6f" (srCertifyTime r)
    , printf "%.4f" (srOverhead r)
    , printf "%.4f" (srOverheadGeo r)
    , printf "%.4f" (srOverheadLo r)
    , printf "%.4f" (srOverheadHi r)
    , show (srAllCertified r)
    ]

instanceCsvHeader :: String
instanceCsvHeader =
  "script,instance,pre_size,post_size,ann_size,checkpoints,certified,\
  \certify_time_s,inline_time_s,inline_forced_time_s"

instanceCsvRow :: String -> InstanceRow -> String
instanceCsvRow script r =
  intercalate
    ","
    [ script
    , show (irIndex r)
    , show (irPreSize r)
    , show (irPostSize r)
    , show (irAnnSize r)
    , show (irCheckpoints r)
    , show (irCertified r)
    , printf "%.6f" (irCertifyTime r)
    , printf "%.6f" (irInlineTime r)
    , printf "%.6f" (irInlineForcedTime r)
    ]

printTable :: [ScriptRow] -> IO ()
printTable rows = do
  printf
    "%-25s %8s %8s %8s %5s %11s %12s %11s %22s %4s\n"
    "script"
    "pre"
    "post"
    "ann"
    "#inl"
    "inline(s)"
    "certify(s)"
    "cert/inl"
    "ann overhead"
    "ok"
  mapM_ printRow rows
  let totalCertify = sum (map srCertifyTime rows)
      totalInline = sum (map srInlineTime rows)
      totalForced = sum [srOverhead r * srInlineTime r | r <- rows]
  printf
    "%-25s %8d %8d %8d %5d %11.4f %12.4f %10.0f%% %22s %4s\n"
    "TOTAL"
    (sum (map srPreSize rows))
    (sum (map srPostSize rows))
    (sum (map srAnnSize rows))
    (sum (map srInstances rows))
    totalInline
    totalCertify
    (totalCertify / totalInline * 100)
    (printf "%.1f%%" (pct (totalForced / totalInline)) :: String)
    (if all srAllCertified rows then "yes" else "NO")
  where
    printRow r =
      printf
        "%-25s %8d %8d %8d %5d %11.4f %12.4f %10.0f%% %22s %4s\n"
        (srScript r)
        (srPreSize r)
        (srPostSize r)
        (srAnnSize r)
        (srInstances r)
        (srInlineTime r)
        (srCertifyTime r)
        (srCertifyTime r / srInlineTime r * 100)
        (overheadCell r)
        (if srAllCertified r then "yes" else "NO")
    -- Cost-weighted overhead, with the per-instance geometric mean in
    -- parentheses. The raw per-instance min/max range is in the CSV; it is
    -- dominated by measurement noise on the cheap fixpoint rounds.
    overheadCell r =
      printf
        "%.1f%% (geo %.1f%%)"
        (pct (srOverhead r))
        (pct (srOverheadGeo r))
        :: String

main :: IO ()
main = do
  args <- getArgs
  (budget, batches) <- case args of
    [] -> pure (1.0, 3)
    [b] -> pure (read b, 3)
    [b, n] -> pure (read b, read n)
    _ -> die "usage: certifier-inline-table [BUDGET_SECS] [BATCHES]"
  initializeTime
  hPutStrLn stderr $
    printf "budget=%.2fs per batch, %d batches per quantity" budget batches
  results <- mapM (processScript budget batches) testScripts
  let scriptRows = map fst results
  putStrLn ""
  printTable scriptRows
  writeFile "inline-table.tex" (texTable scriptRows)
  writeFile "inline-table.csv" . unlines $
    scriptCsvHeader : map scriptCsvRow scriptRows
  writeFile "inline-instances.csv" . unlines $
    instanceCsvHeader
      : [instanceCsvRow (srScript s) r | (s, rs) <- results, r <- rs]
  putStrLn "\nwrote inline-table.tex, inline-table.csv and inline-instances.csv"
