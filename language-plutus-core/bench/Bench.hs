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
                      [ bench "addInteger" $ nf parse f
                      , bench "stringLiteral" $ nf parse g
                      ]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                  let typeCheckConcrete :: Program TyName Name AlexPosn -> Either (Error AlexPosn) (Normalized (Type TyName ()))
                      typeCheckConcrete = runQuoteT . inferTypeOfProgram defOffChainConfig
                      parsed :: BSL.ByteString -> Either (Error AlexPosn) (Program TyName Name AlexPosn)
                      parsed = runQuoteT . parseScoped
                      mkBench = bench "typeCheck" . nf (typeCheckConcrete =<<) . parsed
                  in

                   bgroup "type-check" $ mkBench <$> [f, g, h]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                   let mkBench = bench "check" . nf (fmap check) . parse
                   in
                   bgroup "normal-form check" $ mkBench <$> [f, g, h]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    let renameConcrete :: Program TyName Name AlexPosn -> Program TyName Name AlexPosn
                        renameConcrete = runQuote . rename
                        mkBench = bench "rename" . nf (fmap renameConcrete) . parse
                    in

                    bgroup "renamer" $ mkBench <$> [f, g, h]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    let mkBench src = bench "serialise" $ nf (fmap (serialise . void)) $ parse src
                    in

                    bgroup "CBOR" $ mkBench <$> [f, g, h]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    let deserialiseProgram :: BSL.ByteString -> Program TyName Name ()
                        deserialiseProgram = deserialise
                        parseAndSerialise :: BSL.ByteString -> Either (ParseError AlexPosn) BSL.ByteString
                        parseAndSerialise = fmap (serialise . void) . parse
                        mkBench src = bench "deserialise" $ nf (fmap deserialiseProgram) $ parseAndSerialise src
                    in

                    bgroup "CBOR" $ mkBench <$> [f, g, h]

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
