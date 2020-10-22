module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCek)

import           Control.Monad                              (void)
import qualified Data.ByteString.Lazy                       as BSL
import           Weigh

main :: IO ()
main = do
    ~(f, g) <- evalFiles
    let processor :: BSL.ByteString -> Either (Error DefaultUni DefaultFun AlexPosn) (Term TyName Name DefaultUni DefaultFun ())
        processor contents = toTerm . void <$> runQuoteT (parseScoped contents)
        f' = processor f
        g' = processor g

    mainWith $ sequence_
        [ func "valid" (fmap (unsafeEvaluateCek defBuiltinsRuntime)) f'
        , func "invalid" (fmap (unsafeEvaluateCek defBuiltinsRuntime)) g'
        ]

    where evalFile0 = BSL.readFile "test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
