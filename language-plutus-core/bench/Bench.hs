module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy as BSL
import           Language.PlutusCore

main :: IO ()
main =
    defaultMain [ env envFile $ \ f ->
                  bgroup "format"
                      [ bench "format" $ nf format f ]
                , env envFile $ \ f ->
                  bgroup "parse"
                      [ bench "parse" $ nf parse f ]
                ]
    where envFile = BSL.readFile "test/data/addInteger.pls"
