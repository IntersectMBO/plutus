module Main (main) where

import qualified Bazel.Runfiles             as Runfiles
import           Codec.Serialise
import           Control.Monad
import           Criterion.Main
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.Text                  as T
import           Language.PlutusCore
import           Language.PlutusCore.Pretty
import           System.FilePath            ((</>))

main :: IO ()
main = do
    mr <- Runfiles.createMaybe
    let testDir = case mr of
                    Just r  -> Runfiles.rlocation r "plutus/language-plutus-core/"
                    Nothing -> "."

        envFile = BSL.readFile (testDir </> "test/data/addInteger.plc")
        stringFile = BSL.readFile (testDir </> "test/data/stringLiteral.plc")
        files = (,) <$> envFile <*> stringFile
        largeTypeFile = BSL.readFile (testDir </> "test/types/negation.plc")
        cfg = defPrettyConfigPlcClassic defPrettyConfigPlcOptions
        typeCompare0 = BSL.readFile (testDir </> "test/types/example.plc")
        typeCompare1 = BSL.readFile (testDir </> "bench/example-compare.plc")
        typeCompare = (,) <$> typeCompare0 <*> typeCompare1

    defaultMain [ env envFile $ \ f ->
                  bgroup "format"
                      [ bench "format" $ nf (format cfg :: BSL.ByteString -> Either (Error AlexPosn) T.Text) f ]
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
                    [ bench "writeProgram" $ nf (fmap (serialise . void)) $ parse g
                    ]
                ]
