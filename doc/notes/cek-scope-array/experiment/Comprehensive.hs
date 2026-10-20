{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.DeepSeq (force)
import Control.Exception (SomeException, catch, evaluate)
import Control.Monad (forM, forM_, replicateM_, unless)
import Data.ByteString qualified as BS
import Data.IORef
import Data.List (sort)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats
import PlutusBenchmark.Common qualified as Common
import PlutusBenchmark.Marlowe.BenchUtil qualified as Marlowe
import PlutusBenchmark.Marlowe.Types qualified as M
import PlutusBenchmark.NoFib.Clausify qualified as Clausify
import PlutusBenchmark.NoFib.Knights qualified as Knights
import PlutusBenchmark.NoFib.Prime qualified as Prime
import PlutusBenchmark.NoFib.Queens qualified as Queens
import PlutusBenchmark.Validation.Common qualified as Validation
import PlutusCore.Default
import PlutusCore qualified as PLC
import PlutusCore.DeBruijn (FreeVariableError)
import PlutusCore.Evaluation.Machine.ExBudget (enormousBudget, unExRestrictingBudget)
import PlutusLedgerApi.Common qualified as Ledger
import PlutusLedgerApi.Common.Versions (futurePV)
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import System.CPUTime (getCPUTime)
import System.Directory (listDirectory)
import System.Environment (getArgs)
import System.FilePath ((</>), dropExtension, takeExtension)
import System.IO (BufferMode (LineBuffering), hSetBuffering, isEOF, stdout)
import System.Mem (performGC)
import Text.Printf (printf)
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Check.Scope (ScopeCheckMode (Full), checkScope)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as C

type Term = Common.Term
type FullInput = (V1.SerialisedScript, [V1.Data])
data Spec = Spec String String (IO (Term, Maybe FullInput))
data Loaded = Loaded !String !Term !(Maybe FullInput)

validationCekCtx :: Ledger.EvaluationContext
validationCekCtx = Common.mkEvalCtx Ledger.PlutusV3 DefaultFunSemanticsVariantE
{-# NOINLINE validationCekCtx #-}

validationFullCtx :: Ledger.EvaluationContext
validationFullCtx = Common.mkEvalCtx Ledger.PlutusV1 DefaultFunSemanticsVariantA
{-# NOINLINE validationFullCtx #-}

otherCtx :: Ledger.EvaluationContext
otherCtx = Common.mkMostRecentEvalCtx
{-# NOINLINE otherCtx #-}

getCtx :: String -> Ledger.EvaluationContext
getCtx "validation" = validationCekCtx
getCtx "force-delay" = validationCekCtx
getCtx _ = otherCtx

flatSpecs :: FilePath -> String -> IO [Spec]
flatSpecs root suite = do
  let dir = root </> suite </> "data"
  files <- sort . filter ((==".flat") . takeExtension) <$> listDirectory dir
  forM files $ \file -> pure $ Spec suite (suite ++ "/" ++ dropExtension file) $ do
    bytes <- BS.readFile (dir </> file)
    let U.Program () ver body = Validation.unsafeUnflat file bytes
        term = Common.toNamedDeBruijnTerm body
        full = if suite == "validation" then
          let (script, args) = Validation.peelDataArguments body
           in Just (V1.serialiseUPLC (U.Program () ver script), args)
          else Nothing
    pure (term, full)

marloweSpecs :: FilePath -> String -> IO [Spec]
marloweSpecs root kind = do
  validator <- Marlowe.readFlat (root </> "marlowe/scripts" </> kind </> "validator/sop.flat")
  cases <- either error id <$> (if kind == "semantics" then Marlowe.semanticsBenchmarks else Marlowe.rolePayoutBenchmarks)
  pure [Spec ("marlowe-" ++ kind)
    ("marlowe/" ++ kind ++ "/" ++ show (V2.txInfoId (V2.scriptContextTxInfo (M.bScriptContext bm))))
    (pure (U._progTerm (Marlowe.benchmarkToUPLC validator bm), Nothing)) | bm <- cases]

nofibSpecs :: [Spec]
nofibSpecs = [Spec "nofib" ("nofib/" ++ name) (pure (term, Nothing)) | (name,term) <-
  [("clausify/formula" ++ show i, Clausify.mkClausifyTerm f)
    | (i,f) <- zip [1::Int ..] [Clausify.F1,Clausify.F2,Clausify.F3,Clausify.F4,Clausify.F5]] ++
  [("knights/" ++ show n ++ "x" ++ show n, Knights.mkKnightsTerm 100 n) | n <- [4,6,8]] ++
  [("primetest/" ++ name ++ "digits", Prime.mkPrimalityBenchTerm p)
    | (name,p) <- [("05",Prime.P5),("10",Prime.P10),("30",Prime.P30),("50",Prime.P50)]] ++
  [("queens" ++ show n ++ "x" ++ show n ++ "/" ++ name, Queens.mkQueensTerm n algorithm)
    | n <- [4,5], (name,algorithm) <- [("bt",Queens.Bt),("bm",Queens.Bm),("bjbt1",Queens.Bjbt1),("bjbt2",Queens.Bjbt2),("fc",Queens.Fc)]]]

load :: Spec -> IO Loaded
load (Spec suite _ action) = do
  (term, full) <- action
  !term' <- evaluate (force term)
  !full' <- evaluate (force full)
  unless ((checkScope Full term' :: Either FreeVariableError ()) == Right ()) (error "scope check failed")
  pure (Loaded suite term' full')

runWork :: String -> Loaded -> ()
runWork "cek" (Loaded suite term _) = case Common.evaluateCekLikeInProd (getCtx suite) term of
  Left e -> error (show e)
  Right _ -> ()
runWork "full" (Loaded _ _ (Just (script,args))) =
  case snd $ V1.evaluateScriptRestricting futurePV Ledger.Quiet validationFullCtx
    (unExRestrictingBudget enormousBudget)
    (either (error . show) id (V1.deserialiseScript futurePV script)) args of
      Left e -> error (show e)
      Right _ -> ()
runWork _ _ = error "invalid workload mode"
{-# NOINLINE runWork #-}

checkWork :: Loaded -> String
checkWork (Loaded suite term _) =
  let report = Ledger.evaluateTerm C.counting
        (Ledger.ledgerLanguageIntroducedIn Ledger.PlutusV1) PLC.latestVersion Ledger.Verbose (getCtx suite) term
   in case C.cekResultToEither (C._cekReportResult report) of
        Left e -> error (show e)
        Right result -> show (result, C._cekReportCost report, C._cekReportLogs report)
{-# NOINLINE checkWork #-}

checkFullWork :: Loaded -> String
checkFullWork (Loaded _ _ (Just (script,args))) =
  let report = V1.evaluateScriptRestricting futurePV Ledger.Verbose validationFullCtx
        (unExRestrictingBudget enormousBudget)
        (either (error . show) id (V1.deserialiseScript futurePV script)) args
   in case snd report of
        Left e -> error (show e)
        Right _ -> show report
checkFullWork _ = error "full check requires a validation script"
{-# NOINLINE checkFullWork #-}

loop :: IORef Loaded -> String -> Int -> IO ()
loop ref mode reps = replicateM_ reps (readIORef ref >>= evaluate . runWork mode)

calibrate :: IORef Loaded -> String -> Double -> IO Int
calibrate ref mode target = go 1
  where
    go reps = do
      before <- getMonotonicTimeNSec
      loop ref mode reps
      after <- getMonotonicTimeNSec
      let elapsed = fromIntegral (after-before)/1e9
      if elapsed < 0.005 then go (reps*2)
        else pure (max 1 (ceiling (fromIntegral reps*target/elapsed)))

sample :: IORef Loaded -> String -> Int -> IO ()
sample ref mode reps = do
  performGC
  beforeStats <- getRTSStats
  beforeCpu <- getCPUTime
  before <- getMonotonicTimeNSec
  loop ref mode reps
  after <- getMonotonicTimeNSec
  afterCpu <- getCPUTime
  midStats <- getRTSStats
  performGC
  afterStats <- getRTSStats
  let per x = x / fromIntegral reps :: Double
  printf "%d\t%.12g\t%.12g\t%.6f\t%.12g\t%.12g\t%.8f\n" reps
    (per (fromIntegral (after-before)/1e9))
    (per (fromIntegral (afterCpu-beforeCpu)/1e12))
    (per (fromIntegral (allocated_bytes afterStats-allocated_bytes beforeStats)))
    (per (fromIntegral (gc_cpu_ns midStats-gc_cpu_ns beforeStats)/1e9))
    (per (fromIntegral (gc_elapsed_ns midStats-gc_elapsed_ns beforeStats)/1e9))
    (per (fromIntegral (gcs midStats-gcs beforeStats)))

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  [mode,root] <- getArgs
  specs <- concat <$> sequence [flatSpecs root "validation", flatSpecs root "force-delay",
    marloweSpecs root "semantics", marloweSpecs root "rolepayout", pure nofibSpecs]
  if mode == "catalog" then
    forM_ (zip [0::Int ..] specs) $ \(i,Spec suite name _) -> printf "%d\t%s\t%s\n" i suite name
  else do
    unlessM getRTSStatsEnabled (error "server needs +RTS -T")
    _ <- evaluate validationCekCtx
    _ <- evaluate validationFullCtx
    _ <- evaluate otherCtx
    cache <- newIORef Nothing
    let getInput i = do
          cached <- readIORef cache
          case cached of
            Just (j,ref) | j==i -> pure ref
            _ -> do
              ref <- load (specs !! i) >>= newIORef
              writeIORef cache (Just (i,ref))
              pure ref
        handleCommand line = case words line of
          ["check",i] -> do
            ref <- getInput (read i)
            result <- readIORef ref >>= evaluate . force . checkWork
            putStrLn ("ok\t" ++ show result)
          ["full-check",i] -> do
            ref <- getInput (read i)
            result <- readIORef ref >>= evaluate . force . checkFullWork
            putStrLn ("ok\t" ++ show result)
          ["calibrate",i,kind,target] -> do
            ref <- getInput (read i)
            reps <- calibrate ref kind (read target)
            print reps
          ["sample",i,kind,reps] -> do
            ref <- getInput (read i)
            sample ref kind (read reps)
          _ -> error ("bad command: " ++ line)
        serve = do
          done <- isEOF
          unless done $ do
            line <- getLine
            handleCommand line `catch` (\(e :: SomeException) -> putStrLn ("error\t" ++ show (show e)))
            serve
    putStrLn ("ready\t" ++ show (length specs))
    serve

unlessM :: IO Bool -> IO () -> IO ()
unlessM test action = test >>= (`unless` action)
