module Main (main) where

import           Codec.Serialise
import           Control.Monad
import           Criterion.Main
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.Text                  as T
import           Language.PlutusCore
import           Language.PlutusCore.Pretty

main :: IO ()
main =
    defaultMain [ env envFile $ \ f ->
                    bgroup "format"
                      [ bench "format" $ nf (format cfg :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f
                      ]

                , env typeCompare $ \ ~(f, g) ->
                  let parsed0 = parse f
                      parsed1 = parse g
                  in
                    bgroup "equality"
                        [ bench "Program equality" $ nf ((==) <$> parsed0 <*>) parsed1
                        ]

                , env files $ \ ~(f, g) ->
                    bgroup "parse"
                      [ bench "parse (addInteger)" $ nf parse f
                      , bench "parse (stringLiteral)" $ nf parse g
                      ]

                , env largeTypeFiles $ \ ~(f, g) ->
                   bgroup "type-check"
                      [ bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f
                      , bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) g
                      ]

                , env largeTypeFiles $ \ ~(f, g) ->
                   bgroup "normal-form check"
                      [ bench "check" $ nf (fmap check) (parse f)
                      , bench "check" $ nf (fmap check) (parse g)
                      ]

                , env largeTypeFiles $ \ ~(f, g) ->
                    bgroup "CBOR"
                      [ bench "writeProgram" $ nf (fmap (serialise . void)) $ parse f
                      , bench "writeProgram" $ nf (fmap (serialise . void)) $ parse g
                      ]

                ]

    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          largeTypeFile0 = BSL.readFile "test/types/negation.plc"
          largeTypeFile1 = BSL.readFile "test/types/tail.plc"
          largeTypeFiles = (,) <$> largeTypeFile0 <*> largeTypeFile1
          cfg = defPrettyConfigPlcClassic defPrettyConfigPlcOptions
          typeCompare0 = BSL.readFile "test/types/example.plc"
          typeCompare1 = BSL.readFile "bench/example-compare.plc"
          typeCompare = (,) <$> typeCompare0 <*> typeCompare1
