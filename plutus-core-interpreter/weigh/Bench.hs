module Main (main) where

import           Control.Monad                              (void)
import qualified Data.ByteString.Lazy                       as BSL
import           Language.PlutusCore
import           Language.PlutusCore.Interpreter.CekMachine (runCek)
import           Weigh

main :: IO ()
main = do
    ~(f, g) <- evalFiles
    let processor :: BSL.ByteString -> Either (Error AlexPosn) (Program TyName Name ())
        processor contents = void <$> (runQuoteT $ parseScoped contents)
        f' = processor f
        g' = processor g

    mainWith $ sequence_
        [ func "valid" (fmap (runCek mempty)) f'
        , func "valid" (fmap (runCek mempty)) g'
        ]

    where evalFile0 = BSL.readFile "../language-plutus-core/test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "../language-plutus-core/test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
