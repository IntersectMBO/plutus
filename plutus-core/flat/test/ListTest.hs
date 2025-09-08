{-# LANGUAGE CPP #-}
module Main where

import Flat

#ifdef ETA_VERSION
import Data.Function (trampoline)
import GHC.IO (trampolineIO)
#else
trampoline = id
trampolineIO = id
#endif


longBools = replicate 1000000 False

main = do
    print $ length longBools
    print $ (flat longBools)
