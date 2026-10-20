{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
module ClosureChecks where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM, forM_, unless)
import Data.Text (Text)
import Data.Vector qualified as V
import Main qualified as B
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.MkPlc (mkConstant)
import System.Environment (getArgs)
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as C

-- These integer-producing terms deliberately retain environments across
-- nested arguments, constructors, cases, delays, and polymorphic builtins.
generated :: Int -> Int -> Int -> B.Term
generated seed height depth
  | height == 0 = if depth > 0 && odd seed
      then B.var (1 + seed `mod` depth) else B.int (fromIntegral (seed `mod` 97))
  | otherwise = case seed `mod` 8 of
      0 -> B.add a b
      1 -> B.letIn a (generated s1 (height-1) (depth+1))
      2 -> B.app (B.lam (generated s2 (height-1) (depth+1))) a
      3 -> U.Force () (U.Delay () a)
      4 -> B.app (choose (B.lam (generated s1 (height-1) (depth+1)))
                         (B.lam (generated s2 (height-1) (depth+1)))) a
      5 -> U.Case () (U.Constr () 0 [a,b])
          (V.singleton (B.lam (B.lam (generated s1 (height-1) (depth+2)))))
      6 -> B.letIn (U.Delay () a) (B.add (U.Force () (B.var 1)) (U.Force () (B.var 1)))
      _ -> U.Force () (choose (U.Delay () a) (U.Delay () b))
  where
    next s = (s * 48271 + 1) `mod` 2147483647
    s1 = next seed
    s2 = next s1
    a = generated s1 (height-1) depth
    b = generated s2 (height-1) depth
    choose x y = B.app (B.app (B.app (U.Force () (U.Builtin () IfThenElse))
                           (mkConstant () (odd seed))) x) y

traceInt :: Text -> B.Term -> B.Term
traceInt message = B.app (B.app (U.Force () (U.Builtin () Trace)) (mkConstant () message))

focused :: [(String, B.Term)]
focused =
  [ ("argument-creates-closure", B.letIn (B.int 11) $
      B.app (B.lam (B.app (B.var 1) B.unit))
        (B.letIn (B.int 22) (B.lam (B.add (B.var 2) (B.var 3)))))
  , ("constructor-retains-closures", B.letIn (B.int 11) $
      U.Case () (U.Constr () 0
        [ B.letIn (B.int 22) (B.lam (B.add (B.var 2) (B.var 3)))
        , B.letIn (B.int 44) (B.lam (B.add (B.var 2) (B.var 3))) ])
        (V.singleton (B.lam (B.lam (B.add
          (B.app (B.var 2) B.unit) (B.app (B.var 1) B.unit))))))
  , ("partially-applied-builtin-retains-closure", B.letIn (B.int 11) $
      B.letIn (B.app (B.app (U.Force () (U.Builtin () IfThenElse)) (mkConstant () True))
        (B.letIn (B.int 22) (B.lam (B.var 2)))) $
      B.app (B.app (B.var 1) (B.letIn (B.int 44) (B.lam (B.var 2)))) B.unit)
  , ("returned-constructor-with-delayed-captures", B.letIn (B.int 11) $
      U.Constr () 0 [B.letIn (B.int 22) (U.Delay () (B.var 1)),
                    B.letIn (B.int 44) (B.lam (B.var 2))])
  , ("trace-order", B.app (B.lam (traceInt "body" (B.var 1)))
      (traceInt "argument" (B.int 11)))
  , ("failing-argument", B.app (B.lam (traceInt "unreachable" B.unit)) (U.Error ()))
  , ("bad-force-cause", U.Force () (B.letIn (B.int 11) (B.lam (B.var 2))))
  , ("bad-application-cause", B.app (B.letIn (B.int 11) (U.Delay () (B.var 1))) B.unit)
  , ("bad-case-cause", U.Case () (B.letIn (B.int 11) (B.lam (B.var 2))) V.empty)
  , ("open-under-erased-lambda", B.app (B.lam (B.var 2)) B.unit)
  , ("zero-under-erased-delay", U.Force () (U.Delay () (B.var 0)))
  ]

cases :: [(String, B.Term)]
cases = focused ++ [("generated-" ++ show s, generated s 7 0) | s <- [1..256]]

render mode term = let report = C.runCekDeBruijn B.params mode C.logEmitter term in
  show (C.cekResultToEither (C._cekReportResult report)) ++ "\t" ++
  show (C._cekReportCost report) ++ "\t" ++ show (C._cekReportLogs report)

main :: IO ()
main = do
  args <- getArgs
  terms <- evaluate (force cases)
  _ <- evaluate (force B.params)
  let rows = [(n ++ "/count", render C.counting t) | (n,t) <- terms] ++
        [(n ++ "/budget-" ++ show budget,
          render (C.restricting (ExRestrictingBudget (ExBudget (fromInteger budget) 1000000000))) t)
        | (n,t) <- terms, budget <- [0,100,100000,1000000,10000000]]
  -- Independent evaluations of the same shared AST must not share mutable
  -- environments. Fully discharge after other evaluations have completed.
  if args == ["concurrent"] then do
    pending <- forM (take 64 terms) $ \(_,t) -> do
      done <- newEmptyMVar
      _ <- forkIO (evaluate (force (render C.counting t)) >>= putMVar done)
      pure (t,done)
    forM_ pending $ \(t,done) -> do
      actual <- takeMVar done
      expected <- evaluate (force (render C.counting t))
      unless (actual == expected) (error "cross-evaluation mutation")
    putStrLn "PASS: 64 concurrent evaluations of shared ASTs"
  else forM_ rows $ \(n,row) -> putStrLn (n ++ "\t" ++ row)
