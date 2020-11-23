{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCek)
import           Language.PlutusCore.Evaluation.Machine.Ck  (unsafeEvaluateCk)
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty

-- import           Codec.Serialise
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Criterion.Main
import           Crypto
import qualified Data.ByteString                            as BS
import qualified Data.ByteString.Lazy                       as BSL

pubKey, sig, msg :: BS.ByteString
sig = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
pubKey = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
msg = ""

parse :: BSL.ByteString -> Either (ParseError AlexPosn) (Program TyName Name DefaultUni DefaultFun AlexPosn)
parse str = runQuote $ runExceptT $ flip evalStateT emptyIdentifierState $ parseProgram str

main :: IO ()
main =
    defaultMain [ env largeTypeFiles $ \ ~(f, g, h) ->
                    let mkBench = bench "pretty" . nf (fmap (show . prettyPlcDef)) . parse
                    in

                    bgroup "prettyprint" $ mkBench <$> [f, g, h]

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

                -- , env sampleScript $ \ f ->
                --   let typeCheckConcrete :: Program TyName Name DefaultUni DefaultFun () -> Either (Error DefaultUni DefaultFun ()) (Normalized (Type TyName DefaultUni ()))
                --       typeCheckConcrete p = runQuoteT $ do
                --             tcConfig <- getDefTypeCheckConfig ()
                --             inferTypeOfProgram tcConfig p
                --       mkBench = bench "type-check" . nf typeCheckConcrete . deserialise
                --   in

                --   bgroup "type-check" $ mkBench <$> [f]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                  let typeCheckConcrete :: Program TyName Name DefaultUni DefaultFun AlexPosn -> Either (Error DefaultUni DefaultFun AlexPosn) (Normalized (Type TyName DefaultUni ()))
                      typeCheckConcrete p = runQuoteT $ do
                            tcConfig <- getDefTypeCheckConfig topAlexPosn
                            inferTypeOfProgram tcConfig p
                      mkBench = bench "type-check" . nf (typeCheckConcrete =<<) . runQuoteT . parseScoped
                  in

                   bgroup "type-check" $ mkBench <$> [f, g, h]

                -- , env sampleScript $ \ f ->
                --     let renameConcrete :: Program TyName Name DefaultUni DefaultFun () -> Program TyName Name DefaultUni DefaultFun ()
                --         renameConcrete = runQuote . rename
                --         mkBench = bench "rename (Plutus Tx)" . nf renameConcrete . deserialise
                --   in

                --   bgroup "renamer" $ mkBench <$> [f]

                , env largeTypeFiles $ \ ~(f, g, h) ->
                    let renameConcrete :: Program TyName Name DefaultUni DefaultFun AlexPosn -> Program TyName Name DefaultUni DefaultFun AlexPosn
                        renameConcrete = runQuote . rename
                        mkBench = bench "rename" . nf (fmap renameConcrete) . parse
                    in

                    bgroup "renamer" $ mkBench <$> [f, g, h]

                -- , env largeTypeFiles $ \ ~(f, g, h) ->
                --     let mkBench src = bench "serialise" $ nf (fmap (serialise . void)) $ parse src
                --     in

                --     bgroup "CBOR" $ mkBench <$> [f, g, h]

                -- , env largeTypeFiles $ \ ~(f, g, h) ->
                --     let deserialiseProgram :: BSL.ByteString -> Program TyName Name DefaultUni DefaultFun ()
                --         deserialiseProgram = deserialise
                --         parseAndSerialise :: BSL.ByteString -> Either (ParseError AlexPosn) BSL.ByteString
                --         parseAndSerialise = fmap (serialise . void) . parse
                --         mkBench src = bench "deserialise" $ nf (fmap deserialiseProgram) $ parseAndSerialise src
                --     in

                --     bgroup "CBOR" $ mkBench <$> [f, g, h]

                , env evalFiles $ \ ~(f, g) ->
                    let processor :: BSL.ByteString -> Either (Error DefaultUni DefaultFun AlexPosn) (Program TyName Name DefaultUni DefaultFun ())
                        processor contents = void <$> (runQuoteT $ parseScoped contents)
                        f' = processor f
                        g' = processor g
                    in

                    bgroup "unsafeEvaluateCk"
                      [ bench "valid" $ nf (fmap $ unsafeEvaluateCk defBuiltinsRuntime . toTerm) f'
                      , bench "invalid" $ nf (fmap $ unsafeEvaluateCk defBuiltinsRuntime . toTerm) g'
                      ]
                , env evalFiles $ \ ~(f, g) ->
                   let processor :: BSL.ByteString -> Either (Error DefaultUni DefaultFun AlexPosn) (Program TyName Name DefaultUni DefaultFun ())
                       processor contents = void <$> (runQuoteT $ parseScoped contents)
                       f' = processor f
                       g' = processor g
                   in

                   bgroup "unsafeEvaluateCek"
                     [ bench "valid" $ nf (fmap $ unsafeEvaluateCek defBuiltinsRuntime . toTerm) f'
                     , bench "invalid" $ nf (fmap $ unsafeEvaluateCek defBuiltinsRuntime . toTerm) g'
                     ]
                ,   bgroup "verifySignature" $
                      let verify :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Maybe Bool
                          verify = verifySignature
                      in

                      [ bench "valid" $ nf (verify pubKey msg) sig
                      , bench "invalid" $ nf (verify msg pubKey) sig
                      ]

                ]

    where envFile = BSL.readFile "test/data/addInteger.plc"
          stringFile = BSL.readFile "test/data/stringLiteral.plc"
          files = (,) <$> envFile <*> stringFile
          largeTypeFile0 = BSL.readFile "test/types/negation.plc"
          largeTypeFile1 = BSL.readFile "test/types/tail.plc"
          largeTypeFile2 = BSL.readFile "test/types/verifyIdentity.plc"
          largeTypeFiles = (,,) <$> largeTypeFile0 <*> largeTypeFile1 <*> largeTypeFile2
          typeCompare0 = BSL.readFile "test/types/example.plc"
          typeCompare1 = BSL.readFile "bench/example-compare.plc"
          typeCompare = (,) <$> typeCompare0 <*> typeCompare1
          evalFile0 = BSL.readFile "test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
          -- sampleScript = BSL.readFile "bench/script.plci"
