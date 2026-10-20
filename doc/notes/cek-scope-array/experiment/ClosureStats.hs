{-# LANGUAGE ImportQualifiedPost #-}
module ClosureStats where

import Control.Exception (evaluate)
import Control.DeepSeq (force)
import Control.Monad (forM_)
import Data.List (intercalate)
import Main qualified as B
import System.Environment (getArgs)
import UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv qualified as E

main :: IO ()
main = do
  [dir] <- getArgs
  terms <- B.loadTerms dir
  _ <- evaluate (force B.params)
  putStrLn "name,extensions,buffers,copies,copied_slots,seals,borrows,erased_closures"
  forM_ (terms ++ B.synthetics) $ \(name,t) -> do
    E.resetStats
    _ <- evaluate (B.run t)
    counters <- E.getStats
    putStrLn (name ++ "," ++ intercalate "," (map show counters))
