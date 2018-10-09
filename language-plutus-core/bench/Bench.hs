module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.Text                  as T
import           Language.PlutusCore
import           Language.PlutusCore.Pretty

main :: IO ()
main =
    defaultMain [ env envFile $ \ f ->
                  bgroup "format"
                      [ bench "format" $ nf (format cfg :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f ]
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
                , env typeCompare $ \ f ->
                  let parsed = parse f in
                    bgroup "equality"
                        [ bench "Program equality" $ nf ((==) <$> parsed <*>) parsed
                        ]
                ]
    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          largeTypeFile = BSL.readFile "test/types/negation.plc"
          cfg = defPrettyConfigPlcClassic defPrettyConfigPlcOptions
          typeCompare = BSL.readFile "test/types/example.plc"
