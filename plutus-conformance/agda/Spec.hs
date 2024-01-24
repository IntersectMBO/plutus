-- editorconfig-checker-disable-file
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
-- The entries of the list should be paths from the root of plutus-conformance
-- to the directory containing the test, eg
--   "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"

failingTests :: [FilePath]
failingTests =
    [
     --- byteStringToInteger
      "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/little-endian/all-zeros"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/little-endian/correct-output"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/little-endian/trailing-zeros"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/little-endian/empty"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/big-endian/all-zeros"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/big-endian/leading-zeros"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/big-endian/correct-output"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/big-endian/empty"
    , "test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/both-endian"

    -- integerToByteString
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/negative-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/negative-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/correct-output-exact-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/correct-output-extra-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/too-narrow"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/maximum-width-zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/width-too-big-zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/max-input-width-too-small"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/max-input-fits-max-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/bounded/max-width-input-too-big"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/unbounded/zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/unbounded/negative-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/unbounded/maximum-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/unbounded/input-too-big"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/big-endian/unbounded/correct-output"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/negative-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/negative-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/correct-output-exact-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/correct-output-extra-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/too-narrow"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/maximum-width-zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/width-too-big-zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/max-input-width-too-small"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/max-input-fits-max-width"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/bounded/max-width-input-too-big"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/unbounded/zero"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/unbounded/negative-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/unbounded/maximum-input"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/unbounded/input-too-big"
    , "test-cases/uplc/evaluation/builtin/semantics/integerToByteString/little-endian/unbounded/correct-output"
    ]

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg (\dir -> elem dir failingTests)

