module Main (main) where

import           Control.Monad                              (void)
import           Criterion.Main
import qualified Data.ByteString.Lazy                       as BSL
import           Language.PlutusCore
import           Language.PlutusCore.Interpreter.CekMachine (runCek)

main :: IO ()
main =
    defaultMain [ env evalFiles $ \ ~(f, g) ->
                    let processor :: BSL.ByteString -> Either (Error AlexPosn) (Program TyName Name ())
                        processor contents = void <$> (runQuoteT $ parseScoped contents)
                        f' = processor f
                        g' = processor g
                    in

                    bgroup "runCek"
                      [ bench "valid" $ nf (fmap (runCek mempty)) f'
                      , bench "invalid" $ nf (fmap (runCek mempty)) g'
                      ]

                ]

    where evalFile0 = BSL.readFile "../language-plutus-core/test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "../language-plutus-core/test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
