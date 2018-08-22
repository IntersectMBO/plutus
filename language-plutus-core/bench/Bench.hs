module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy as BSL
import           Language.PlutusCore

-- TODO: benchmark the typechecker!
main :: IO ()
main =
    defaultMain [ env envFile $ \ f ->
                  bgroup "format"
                      [ bench "format" $ nf (format defaultCfg) f ]
                , env files $ \ ~(f, g) ->
                  bgroup "parse"
                      [ bench "parse (addInteger)" $ nf parse f
                      , bench "parse (stringLiteral)" $ nf parse g
                      ]
                , env typeFile $ \ f ->
                   bgroup "type-check"
                      [ bench "fileType" $ nf printType f ]
                ]
    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          typeFile = BSL.readFile "test/types/addIntegerCorrect.plc"
