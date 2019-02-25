module Main (main) where

import           Codec.Serialise
import           Control.Monad
import           Criterion.Main
import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text                                as T
import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine (runCk)
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

                , env largeTypeFiles $ \ ~(f, g, h) ->
                   bgroup "type-check"
                      [ bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f
                      , bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) g
                      , bench "printType" $ nf (printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text) h
                      ]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                   bgroup "normal-form check"
                      [ bench "check" $ nf (fmap check) (parse f)
                      , bench "check" $ nf (fmap check) (parse g)
                      , bench "check" $ nf (fmap check) (parse h)
                      ]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    bgroup "renamer"
                      [ bench "rename" $ nf (fmap renameConcrete) (parse f)
                      , bench "rename" $ nf (fmap renameConcrete) (parse g)
                      , bench "rename" $ nf (fmap renameConcrete) (parse h)
                      ]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    bgroup "CBOR"
                      [ bench "writeProgram" $ nf (fmap (serialise . void)) $ parse f
                      , bench "writeProgram" $ nf (fmap (serialise . void)) $ parse g
                      , bench "writeProgram" $ nf (fmap (serialise . void)) $ parse h
                      ]

                , env evalFiles $ \ ~(f, g) ->
                    let processor :: BSL.ByteString -> Either (Error AlexPosn) (Program TyName Name ())
                        processor contents = void <$> (runQuoteT $ parseScoped contents)
                        f' = processor f
                        g' = processor g
                    in

                    bgroup "runCk"
                      [ bench "valid" $ nf (fmap runCk) f'
                      , bench "invalid" $ nf (fmap runCk) g'
                      ]

                ]

    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          largeTypeFile0 = BSL.readFile "test/types/negation.plc"
          largeTypeFile1 = BSL.readFile "test/types/tail.plc"
          largeTypeFile2 = BSL.readFile "test/types/verifyIdentity.plc"
          largeTypeFiles = (,,) <$> largeTypeFile0 <*> largeTypeFile1 <*> largeTypeFile2
          cfg = defPrettyConfigPlcClassic defPrettyConfigPlcOptions
          typeCompare0 = BSL.readFile "test/types/example.plc"
          typeCompare1 = BSL.readFile "bench/example-compare.plc"
          typeCompare = (,) <$> typeCompare0 <*> typeCompare1
          evalFile0 = BSL.readFile "test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1

renameConcrete :: Program TyName Name AlexPosn -> Program TyName Name AlexPosn
renameConcrete = runQuote . rename
