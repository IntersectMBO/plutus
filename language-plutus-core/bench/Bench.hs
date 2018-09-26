module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text            as T
import           Language.PlutusCore

main :: IO ()
main =
    defaultMain [ env envFile $ \ f ->
                  bgroup "format"
                      [ bench "format" $ nf (format defaultCfg :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f ]
                , env files $ \ ~(f, g) ->
                  bgroup "parse"
                      [ bench "parse (addInteger)" $ nf parse f
                      , bench "parse (stringLiteral)" $ nf parse g
                      ]
                , env largeTypeFile $ \ g ->
                   bgroup "type-check"
                      [ bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) g
                      ]
                , env largeTypeFile $ \ g ->
                   bgroup "normal-form check"
                      [ bench "check" $ nf (fmap check) (parse g)
                      ]
                , env largeTypeFile $ \ g ->
                  bgroup "CBOR"
                    [ bench "writeProgram" $ nf (fmap writeProgram) (parse g)
                    ]
                ]
    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          largeTypeFile = BSL.readFile "test/types/negation.plc"
