{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad (forM_, unless)
import PlutusCore.Default
import PlutusCore.DeBruijn
import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv qualified as E

root :: E.RAList Int
root = E.emptyFor (iterate (U.LamAbs () (NamedDeBruijn "v" (Index 0)))
  (U.Error () :: U.Term NamedDeBruijn DefaultUni DefaultFun ()) !! 64)

check e xs = forM_ (zip [1..] xs) $ \(i,x) -> do
  actual <- E.indexOneM e i
  unless (actual == Just x) (error "borrowed/sealed prefix corrupted")

main :: IO ()
main = do
  a <- E.consM 11 root
  outer <- E.pinM a
  b <- E.consM 22 a
  inner <- E.pinM b
  -- Extension of an older prefix must copy while the deeper borrow is live.
  fork <- E.consM 33 a
  check inner [22,11]
  check fork [33,11]
  b' <- E.unpinM inner
  -- Permanent capture made during the borrow must survive restoring its barrier.
  captured <- E.sealM b'
  _ <- E.unpinM outer
  fork' <- E.consM 44 a
  check captured [22,11]
  check fork' [44,11]
  -- In the absence of captures, repeated calls reuse their stack tail.
  forM_ [1..2000] $ \x -> do
    child <- E.consM x fork'
    held <- E.pinM child
    nested <- E.consM (x+1) child
    check held [x,44,11]
    check nested [x+1,x,44,11]
    _ <- E.unpinM held
    check captured [22,11]
  putStrLn "PASS: nested borrows, restoration, sealed captures, 2000 tail reuses"
