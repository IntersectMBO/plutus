{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module Main where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM, forM_, replicateM_, unless)
import Criterion.Main
import Data.ByteString qualified as BS
import Data.Default.Class (def)
import Data.List (sort)
import Data.IORef
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats
import System.CPUTime (getCPUTime)
import System.Mem (performGC)
import Text.Printf (printf)
import Data.Vector qualified as V
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.DeBruijn (FreeVariableError, Index (..), NamedDeBruijn (..))
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusCore.Flat (unflat)
import System.Directory (listDirectory)
import System.Environment (getArgs, withArgs)
import System.FilePath ((</>), dropExtension, takeExtension)
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Check.Scope (ScopeCheckMode (..), checkScope)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as C

type Term = U.Term NamedDeBruijn DefaultUni DefaultFun ()

scope :: Term -> Either FreeVariableError ()
scope = checkScope Full
{-# NOINLINE scope #-}

-- Fused full scope validation and maximum lexical depth (not maximum index).
-- This is timed separately to expose the price of preparing a fixed array.
capacity :: Term -> Either String Int
capacity = go 0
  where
    go !d = \case
      U.Var _ (NamedDeBruijn _ (Index i))
        | i > 0 && i <= fromIntegral d -> Right d
        | otherwise -> Left "free variable"
      U.LamAbs _ (NamedDeBruijn _ (Index b)) t
        | b == 0 -> go (d + 1) t
        | otherwise -> Left "nonzero binder"
      U.Apply _ f x -> max <$> go d f <*> go d x
      U.Delay _ t -> go d t
      U.Force _ t -> go d t
      U.Constr _ _ ts -> foldl combine (Right d) (map (go d) ts)
      U.Case _ t ts -> foldl combine (go d t) (map (go d) (V.toList ts))
      _ -> Right d
    combine a b = max <$> a <*> b
{-# NOINLINE capacity #-}

params :: DefaultMachineParameters
params = case mkMachineVariantParametersFor [DefaultFunSemanticsVariantE] mempty of
  Left err -> error (show err)
  Right [(_, p)] -> MachineParameters def p
  Right _ -> error "unexpected parameter variants"
{-# NOINLINE params #-}

run :: Term -> ()
run t = case C._cekReportResult (C.runCekDeBruijn params C.restrictingEnormous C.noEmitter t) of
  C.CekFailure e -> error (show e)
  _ -> ()
{-# NOINLINE run #-}

preparedRun :: Term -> ()
preparedRun t = case scope t of
  Left e -> error (show e)
  Right () -> run t
{-# NOINLINE preparedRun #-}

var :: Int -> Term
var = U.Var () . NamedDeBruijn "v" . Index . fromIntegral
lam :: Term -> Term
lam = U.LamAbs () (NamedDeBruijn "v" (Index 0))
app :: Term -> Term -> Term
app = U.Apply ()
letIn :: Term -> Term -> Term
letIn x body = app (lam body) x
int :: Integer -> Term
int = mkConstant ()
unit :: Term
unit = mkConstant () ()
add :: Term -> Term -> Term
add x y = app (app (U.Builtin () AddInteger) x) y

synthetics :: [(String, Term)]
synthetics =
  [ ("closure-alias", makers (lam (var 2)) (\x -> app x unit))
  , ("delay-alias", makers (U.Delay () (var 1)) (U.Force ()))
  , ("case-capture", letIn (int 11) $ U.Case () (U.Constr () 0 [int 22]) (V.singleton (lam (add (var 2) (var 1)))))
  , ("returned-closure", app (lam (lam (var 2))) (int 11))
  , ("returned-delay", app (lam (U.Delay () (var 1))) (int 11))
  ] ++
  [ ("lookup-" ++ show d ++ "-" ++ label,
      foldl app (iterate lam (U.Constr () 0 (replicate 4096 (var i))) !! d) (map int [1 .. fromIntegral d]))
  | d <- [8, 64, 256], (label, i) <- [("near", 1), ("far", d)]
  ] ++
  [ ("extend-" ++ show d, foldl app (iterate lam (var 1) !! d) (map int [1 .. fromIntegral d]))
  | d <- [8, 64, 256]
  ]
  where
    makers body use = letIn (lam body) $
      letIn (app (var 1) (int 11)) $
      letIn (app (var 2) (int 22)) $
      add (use (var 2)) (use (var 1))

loadTerms :: FilePath -> IO [(String, Term)]
loadTerms dir = do
  files <- sort . filter ((== ".flat") . takeExtension) <$> listDirectory dir
  forM files $ \file -> do
    bytes <- BS.readFile (dir </> file)
    let program = case unflat bytes of
          Left e -> error (show e)
          Right (U.UnrestrictedProgram p) -> p
        term = U.termMapNames (\(U.DeBruijn i) -> NamedDeBruijn "v" i) (U._progTerm program)
    t <- evaluate (force term)
    pure (dropExtension file, t)

stats :: Term -> (Int, Int, Int)
stats = go 0
  where
    merge (n, d, i) (n', d', i') = (n+n', max d d', max i i')
    go !d = \case
      U.Var _ (NamedDeBruijn _ (Index i)) -> (1, d, fromIntegral i)
      U.LamAbs _ _ t -> merge (1, d+1, 0) (go (d+1) t)
      U.Apply _ f x -> merge (1,d,0) (merge (go d f) (go d x))
      U.Delay _ t -> merge (1,d,0) (go d t)
      U.Force _ t -> merge (1,d,0) (go d t)
      U.Constr _ _ ts -> foldl merge (1,d,0) (map (go d) ts)
      U.Case _ t ts -> foldl merge (merge (1,d,0) (go d t)) (map (go d) (V.toList ts))
      _ -> (1,d,0)

checkTerm :: (String, Term) -> IO ()
checkTerm (name, t) = do
  -- Mandatory guard before EVERY use of an unchecked experimental evaluator.
  unless (scope t == Right ()) (error ("not fully scoped: " ++ name))
  unless (capacity t == Right (let (_,d,_) = stats t in d)) (error ("capacity mismatch: " ++ name))
  let report = C.runCekDeBruijn params C.counting C.logEmitter t
      result = C.cekResultToEither (C._cekReportResult report)
  case result of
    Left e -> error (name ++ ": " ++ show e)
    Right r -> do
      whenAlias name $ unless (r == int 33) (error ("closure regression: " ++ name))
      putStrLn (name ++ "\t" ++ show result ++ "\t" ++ show (C._cekReportCost report) ++ "\t" ++ show (C._cekReportLogs report))
  where
    whenAlias name act = if name `elem` ["closure-alias", "delay-alias", "case-capture"] then act else pure ()

-- Read the input through IO on every iteration so GHC cannot share a pure
-- evaluation result across repetitions. Timing includes naturally occurring GC.
measure :: Double -> String -> (Term -> a) -> (String, Term) -> IO ()
measure target group action (name, t) = do
  ref <- newIORef t
  let loop n = replicateM_ n (readIORef ref >>= evaluate . action)
      calibrate n = do
        before <- getMonotonicTimeNSec
        loop n
        after <- getMonotonicTimeNSec
        let seconds = fromIntegral (after - before) / 1e9
        if seconds < 0.005 then calibrate (n * 2)
          else pure (max 1 (ceiling (fromIntegral n * target / seconds)))
  reps <- calibrate 1
  performGC
  beforeStats <- getRTSStats
  beforeCpu <- getCPUTime
  before <- getMonotonicTimeNSec
  loop reps
  after <- getMonotonicTimeNSec
  afterCpu <- getCPUTime
  performGC
  afterStats <- getRTSStats
  let perIter x = x / fromIntegral reps :: Double
  printf "%s/%s,%d,%.12g,%.12g,%.6f\n" group name reps
    (perIter (fromIntegral (after - before) / 1e9))
    (perIter (fromIntegral (afterCpu - beforeCpu) / 1e12))
    (perIter (fromIntegral (allocated_bytes afterStats - allocated_bytes beforeStats)))

main :: IO ()
main = do
  mode:dir:args <- getArgs
  real <- loadTerms dir
  synth <- evaluate (force synthetics)
  _ <- evaluate (force params)
  -- Scope proof is prepared outside timed CEK-only runs, just as script preparation is.
  forM_ (real ++ synth) $ \(n,t) -> unless (scope t == Right ()) (error ("scope: " ++ n))
  case mode of
    "check" -> do
      let nestedOpen = U.Constr () 0 [var 1]
          unusedBinders = lam (lam unit)
      unless (scope nestedOpen /= Right () &&
              (checkScope NoCaseConstr nestedOpen :: Either FreeVariableError ()) == Right ())
        (error "legacy/full scope distinction failed")
      unless (capacity unusedBinders == Right 2) (error "unused binders need slots")
      unless (all ((/= Right ()) . scope) [var 0, var 1, lam (var 2)])
        (error "invalid variable passed full scope check")
      mapM_ checkTerm (real ++ synth)
    "stats" -> do
      putStrLn "name,nodes,max_depth,max_index"
      forM_ (real ++ synth) $ \(n,t) -> let (nodes,d,i) = stats t in putStrLn (n ++ "," ++ show nodes ++ "," ++ show d ++ "," ++ show i)
    "sample" -> do
      unlessM getRTSStatsEnabled (error "sample requires +RTS -T")
      let target = read (head args)
          group = args !! 1
      putStrLn "name,reps,seconds,cpu_seconds,allocated_bytes"
      case group of
        "cek" -> do
          mapM_ (measure target "cek" run) real
          mapM_ (measure target "synthetic" run) synth
        "full" -> mapM_ (measure target "scope+cek" preparedRun) real
        "prep" -> do
          mapM_ (measure target "scope" scope) real
          mapM_ (measure target "capacity-forced" (either error id . capacity)) real
        _ -> error "sample group must be cek, full, or prep"
    "bench" -> withArgs args $ defaultMain
      [ bgroup "cek" [bench n (whnf run t) | (n,t) <- real]
      , bgroup "scope+cek" [bench n (whnf preparedRun t) | (n,t) <- real]
      , bgroup "scope" [bench n (whnf scope t) | (n,t) <- real]
      , bgroup "capacity" [bench n (whnf (either error id . capacity) t) | (n,t) <- real]
      , bgroup "synthetic" [bench n (whnf run t) | (n,t) <- synth]
      ]
    _ -> error "usage: Bench (check|stats|bench) script-directory [criterion options]"

unlessM :: IO Bool -> IO () -> IO ()
unlessM test action = test >>= (`unless` action)
