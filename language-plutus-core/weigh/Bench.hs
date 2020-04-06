module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek                 (unsafeEvaluateCek)
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults

import           Control.Monad                                              (void)
import qualified Data.ByteString.Lazy                                       as BSL
import           Weigh

main :: IO ()
main = do
    ~(f, g) <- evalFiles
    let processor :: BSL.ByteString -> Either (Error DefaultUni AlexPosn) (Term TyName Name DefaultUni ())
        processor contents = toTerm . void <$> runQuoteT (parseScoped contents)
        f' = processor f
        g' = processor g

    mainWith $ sequence_
        [ func "valid" (fmap (unsafeEvaluateCek mempty defaultCostModel)) f'
        , func "invalid" (fmap (unsafeEvaluateCek mempty defaultCostModel)) g'
        ]

    where evalFile0 = BSL.readFile "test/Evaluation/Golden/verifySignature.plc"
          evalFile1 = BSL.readFile "test/Evaluation/Golden/verifySignatureError.plc"
          evalFiles = (,) <$> evalFile0 <*> evalFile1
