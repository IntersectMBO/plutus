{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Text hiding (map)
import Data.Text.IO
import PlutusCore as PLC
import PlutusCore.Pretty
import Prelude hiding (readFile)
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.HUnit
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)
import UntypedPlutusCore.Parser as UPLC

main :: IO ()
main = do
    uplcFiles <- findByExtension [".uplc"] "plutus-conformance/uplc/evaluation/textual-inputs"
    lProgInText <- traverse readFile uplcFiles
    defaultMain undefined --(testUplcEvaluationTextual lProg)

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (PLC.defaultVersion ())

evalUplcProg :: UplcProg -> IO (EvaluationResult UplcProg)
evalUplcProg p = pure $
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit PLC.defaultCekParameters (UPLC._progTerm p))

testUplcEvaluation :: (UplcProg -> IO (EvaluationResult UplcProg)) -> TestTree
testUplcEvaluation = undefined

testUplcEvaluationTextual :: (Text -> IO Text) -> TestTree
testUplcEvaluationTextual runner = testUplcEvaluation undefined --(evalUplcProg . UPLC.parseProgram <$> runner . pack . show)

-- runAgdaImpl = callProcess “agdaImpl …”

-- testUplcEvaluation runAgdaImpl
