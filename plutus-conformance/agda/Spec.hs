{-# LANGUAGE TypeApplications #-}
{- | Conformance tests for the Agda implementation. -}
module Main (main) where

import Control.Monad.Trans.Except
import MAlonzo.Code.Main (runUAgda)
import PlutusConformance.Common
import PlutusCore (Error (..))
import PlutusCore.Default
import PlutusCore.Quote
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn

-- | Our `evaluator` for the Agda UPLC tests is the CEK machine.
agdaEvalUplcProg :: UplcProg -> Maybe UplcProg
agdaEvalUplcProg (UPLC.Program () version tmU) =
    let
        -- turn it into an untyped de Bruijn term
        tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
        tmUDB = deBruijnTerm tmU
    in
    case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
        -- if there's an exception, evaluation failed, should return `Nothing`.
        Left _ -> Nothing
        -- evaluate the untyped term with CEK
        Right tmUDBSuccess ->
            case runUAgda tmUDBSuccess of
                Left _ -> Nothing
                Right tmEvaluated ->
                    let tmNamed = runQuote $ runExceptT $
                            withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated
                    in
                    -- turn it back into a named term
                    case tmNamed of
                        Left _          -> Nothing
                        Right namedTerm -> Just $ UPLC.Program () version namedTerm

-- | These tests are currently failing so they are marked as expected to fail.
-- Once a fix for a test is pushed, the test will fail. Remove it from this list.
failingTests :: [FilePath]
failingTests = [
    -- the metatheory for list and pair is not done
    "test-cases/uplc/evaluation/builtin/semantics/mkNilPairData"
    , "test-cases/uplc/evaluation/builtin/semantics/mkNilData"
    -- The tests for consByteString are disabled because the V2 version of
    -- consByteString requires the first argument to be in [0..255].  The V1
    -- version accepts any integer and reduces it modulo 256 before consing.
    -- Agda has the BuiltinVersion=V1 but Haskell defaults to the latest
    -- BuilinVersion.
    , "test-cases/uplc/evaluation/builtin/semantics/consByteString/consByteString1"
    , "test-cases/uplc/evaluation/builtin/semantics/consByteString/consByteString2"

    ]
    -- SOP tests don't work yet, filter out the cases that are supposed to fail,
    -- and therefore succeed by accident
    ++ fmap (\i -> "test-cases/uplc/evaluation/term/case/case-" ++ show @Integer i)
               (filter (\i -> i /= 7) [1..7])
    ++ fmap (\i -> "test-cases/uplc/evaluation/term/constr/constr-" ++ show @Integer i)
               (filter (\i -> i /= 5 && i /= 6) [1..6])

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg (\dir -> elem dir failingTests)

