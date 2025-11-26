{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This benchmark cases measures efficiency of 'Data' construction.
module Main (main) where

import Criterion.Main

import PlutusBenchmark.Common (benchTermCek, getConfig, mkMostRecentEvalCtx)
import PlutusLedgerApi.Common (EvaluationContext)

import PlutusBenchmark.Data qualified as Data

import Control.Exception
import Data.ByteString as BS
import Data.Functor

benchmarks :: EvaluationContext -> [Benchmark]
benchmarks ctx =
  [ bgroup
      "data"
      [ mkBMs "conDeconI" Data.conDeconI
      , mkBMs "conI" Data.conI
      , mkBMs "conDeconB - short" (Data.conDeconB "helloworld")
      , mkBMs "conB - short" (Data.conB "helloworld")
      , mkBMs "conDeconB - long" (Data.conDeconB $ BS.replicate 10000 97)
      , mkBMs "conB - long" (Data.conB $ BS.replicate 10000 97)
      , mkBMs "constr no release, 2000 chuck size" (Data.constrDataNoRelease 2000)
      , mkBMs "constr with release, 2000 chuck size" (Data.constrDataWithRelease 2000)
      , mkBMs "list no release, 2000 chuck size" (Data.listDataNoRelease 2000)
      , mkBMs "list with release, 2000 chuck size" (Data.listDataWithRelease 2000)
      ]
  ]
  where
    mkBMs name f =
      bgroup name $
        [2000, 4000 .. 12000] <&> \n ->
          bench (show n) $ benchTermCek ctx (f n)

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  config <- getConfig 15.0
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith config $ benchmarks evalCtx
