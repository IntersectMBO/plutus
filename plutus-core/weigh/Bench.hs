module Main (main) where

import           Language.PlutusCore
import qualified Language.UntypedPlutusCore                        as UPLC
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCek)

import           Control.Monad                                     (void)
import qualified Data.ByteString.Lazy                              as BSL
import           Weigh

main :: IO ()
main = do
    ~(f, g) <- evalFiles
    let processor :: BSL.ByteString -> Either (Error DefaultUni DefaultFun AlexPosn) (Term TyName Name DefaultUni DefaultFun ())
        processor contents = toTerm . void <$> runQuoteT (parseScoped contents)
        f' = processor f
        g' = processor g

    mainWith $ sequence_
        [ func "valid" (fmap (unsafeEvaluateCek defBuiltinsRuntime . UPLC.erase)) f'
        , func "invalid" (fmap (unsafeEvaluateCek defBuiltinsRuntime . UPLC.erase)) g'
        ]

    where evalFile0 = BSL.readFile "test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
