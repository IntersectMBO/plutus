module Main (main) where

-- import PlutusPrelude

-- import Check.Spec qualified as Check
-- import CostModelInterface.Spec
-- import Evaluation.Spec (test_evaluation)
-- import Names.Spec
-- import Normalization.Check
-- import Normalization.Type
-- import Pretty.Readable
-- import TypeSynthesis.Spec (test_typecheck)

import PlutusCore as TPLC
import PlutusCore.UntypedPlutusCore qualified as UPLC (Program (..))
-- import PlutusCore.DeBruijn
-- import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Evaluation.Result
-- import PlutusCore.Generators
-- import PlutusCore.Generators.AST as AST
-- import PlutusCore.Generators.NEAT.Spec qualified as NEAT
-- import PlutusCore.MkPlc
-- import PlutusCore.Pretty

-- import Data.ByteString.Lazy qualified as BSL
-- import Data.Either (isLeft)
-- import Data.Foldable (for_)
-- import Data.Text qualified as T
-- import Data.Text.Encoding (encodeUtf8)
-- import Data.Text.IO (readFile)
-- import Data.Word (Word64)
-- import Flat (flat, unflat)
-- import Hedgehog hiding (Var)
-- import Hedgehog.Gen qualified as Gen
-- import Hedgehog.Range qualified as Range
-- import Prelude hiding (readFile)
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

main :: IO ()
main = do
    uplcFiles <- findByExtension [".uplc"] "plutus-conformance/uplc/evaluation/textual-inputs"
    defaultMain (testUplcEvaluationTextual uplcFiles)

type UplcProg = UPLC.Program name uni fun ()

-- progToTerm :: UplcProg -> UPLC.Term name uni fun ()
-- progToTerm p = _progTerm p

termToProg :: UPLC.Term name uni fun () -> UplcProg
termToProg = UPLC.Program () (PLC.defaultVersion ())

evalUplcProg :: UplcProg -> IO EvaluationResult UplcProg
evalUplcProg p =
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit TPLC.defaultCekParameters (_progTerm p))

testUplcEvaluation :: (UplcProg -> IO EvaluationResult UplcProg) -> TestTree
testUplcEvaluation = undefined

testUplcEvaluationTextual :: (Text -> IO Text) -> TestTree
testUplcEvaluationTextual runner = testUplcEvaluation (parse <$> runner . prettyprint)

-- runAgdaImpl = callProcess “agdaImpl …”

-- testUplcEvaluation runAgdaImpl
