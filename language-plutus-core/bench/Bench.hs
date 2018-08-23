module Main (main) where

import           Control.Monad        (void)
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
                , env typeFiles $ \ ~(f, g) ->
                   bgroup "type-check"
                      [ bench "printType" $ nf printType f
                      , bench "printType" $ nf printType g
                      ]
                , env largeTypeFile $ \ g ->
                   bgroup "normal-form check"
                      [ bench "check" $ nf (fmap check) (parse g)
                      ]
                , env typeFiles $ \ ~(f, g) ->
                  bgroup "CBOR"
                    [ bench "writeProgram" $ nf (fmap writeProgram) (void <$> parse f)
                    , bench "writeProgram" $ nf (fmap writeProgram) (void <$> parse g)
                    ]
                ]
    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          typeFile = BSL.readFile "test/types/addIntegerCorrect.plc"
          largeTypeFile = BSL.readFile "test/types/negation.plc"
          typeFiles = (,) <$> typeFile <*> largeTypeFile
