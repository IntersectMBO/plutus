{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy  as BSL
import           Language.PlutusNapkin

tinyProgram :: BSL.ByteString
tinyProgram = "[(builtin addInteger) x y]"

main :: IO ()
main =
    defaultMain [ bgroup "format"
                      [ bench "format" $ nf format tinyProgram ]
                ]
