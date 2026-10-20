{-# LANGUAGE CPP #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM, forM_, unless)
import GHC.Exts (toList)
import PlutusCore.Default
import PlutusCore.DeBruijn
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv qualified as E

-- Sixty-four slots when testing fixed arrays, ordinary empty for compact arrays.
-- The runner selects the fixed-capacity constructor with CPP.
emptyEnv :: E.RAList Int
#ifdef FIXED_ARRAY
emptyEnv = E.emptyFor (iterate (U.LamAbs () (NamedDeBruijn "v" (Index 0)))
  (U.Error () :: U.Term NamedDeBruijn DefaultUni DefaultFun ()) !! 64)
#else
emptyEnv = E.empty
#endif

check :: E.RAList Int -> [Int] -> IO ()
check e expected = do
  unless (toList e == expected) (error "snapshot changed")
  forM_ (zip [1..] expected) $ \(i,x) ->
    unless (E.indexOne e i == Just x) (error "wrong variable")
  forM_ [0, fromIntegral (length expected + 1), maxBound] $ \i ->
    unless (E.indexOne e i == Nothing) (error "invalid index accepted")

main :: IO ()
main = do
  let root = emptyEnv
      linear = scanl (flip E.cons) root [1..32]
  forM_ (zip linear [0..32]) $ \(e,n) -> check e (reverse [1..n])
  -- Repeatedly fork old, still-live prefixes; inspect ALL retained snapshots.
  let go 0 _ = pure ()
      go k states = do
        let (parent, xs) = states !! ((k * 7919) `mod` length states)
            (p, ys) = if length xs >= 63 then (root, []) else (parent, xs)
            child = E.cons k p
            states' = take 128 ((child,k:ys):states)
        mapM_ (uncurry check) states'
        go (k-1) states'
  go (2000 :: Int) [(root,[])]
  -- Sibling branches may be forced concurrently; only one may claim a slot.
  let shared = last linear
  slots <- forM [1..64] $ \x -> do
    done <- newEmptyMVar
    _ <- forkIO $ do
      result <- evaluate (force (toList (E.cons x shared)))
      putMVar done result
    pure (x,done)
  forM_ slots $ \(x,done) -> do
    result <- takeMVar done
    unless (result == x:reverse [1..32]) (error "concurrent fork changed prefix")
  check shared (reverse [1..32])
  putStrLn "PASS: retained prefixes, 2000 forks, boundary indices, 64 concurrent siblings"
