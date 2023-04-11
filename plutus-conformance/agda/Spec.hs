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
    -- The tests for the BLS12-381 builtins are disabled because the metatheory
    -- doesn't yet deal with the builtins properly. The commented-out tests will
    -- "succeed" because failure (for a genuine reason) is expected.
     ++ fmap ("test-cases/uplc/evaluation/builtin/semantics/" ++)
     [ "bls12_381_G1_add/add-associative"
     , "bls12_381_G1_add/add-zero"
     , "bls12_381_G1_add/add"
     , "bls12_381_G1_add/add-commutative"
     , "bls12_381_G1_compress/compress"
     , "bls12_381_G1_equal/equal-false"
     , "bls12_381_G1_equal/equal-true"
     , "bls12_381_G1_hashToGroup/hash"
     , "bls12_381_G1_scalarMul/mul0"
     , "bls12_381_G1_scalarMul/mul4x11"
     , "bls12_381_G1_scalarMul/muladd"
     , "bls12_381_G1_scalarMul/mul1"
     , "bls12_381_G1_scalarMul/mul44"
     , "bls12_381_G1_scalarMul/addmul"
     , "bls12_381_G1_scalarMul/mulneg44"
     , "bls12_381_G1_scalarMul/mul19+25"
     , "bls12_381_G1_scalarMul/mulneg1"
     , "bls12_381_G1_scalarMul/mulperiodic1"
     , "bls12_381_G1_scalarMul/mulperiodic2"
     , "bls12_381_G1_scalarMul/mulperiodic3"
     , "bls12_381_G1_scalarMul/mulperiodic4"
     , "bls12_381_G1_neg/neg"
     , "bls12_381_G1_neg/add-neg"
     , "bls12_381_G1_neg/neg-zero"
     , "bls12_381_G1_uncompress/zero"
     -- , "bls12_381_G1_uncompress/on-curve-serialised-not-compressed"
     ---, "bls12_381_G1_uncompress/off-curve"
     -- , "bls12_381_G1_uncompress/bad-zero-1"
     , "bls12_381_G1_uncompress/on-curve-bit3-set"
     -- , "bls12_381_G1_uncompress/too-short"
     -- , "bls12_381_G1_uncompress/out-of-group"
     , "bls12_381_G1_uncompress/on-curve-bit3-clear"
     -- , "bls12_381_G1_uncompress/too-long"
     -- , "bls12_381_G1_uncompress/bad-zero-2"
     -- , "bls12_381_G1_uncompress/bad-zero-3"
     , "bls12_381_G2_add/add-associative"
     , "bls12_381_G2_add/add-zero"
     , "bls12_381_G2_add/add"
     , "bls12_381_G2_add/add-commutative"
     , "bls12_381_G2_compress/compress"
     , "bls12_381_G2_equal/equal-false"
     , "bls12_381_G2_equal/equal-true"
     , "bls12_381_G2_hashToGroup/hash"
     , "bls12_381_G2_scalarMul/mul0"
     , "bls12_381_G2_scalarMul/mul4x11"
     , "bls12_381_G2_scalarMul/muladd"
     , "bls12_381_G2_scalarMul/mul1"
     , "bls12_381_G2_scalarMul/mul44"
     , "bls12_381_G2_scalarMul/addmul"
     , "bls12_381_G2_scalarMul/mulneg44"
     , "bls12_381_G2_scalarMul/mul19+25"
     , "bls12_381_G2_scalarMul/mulneg1"
     , "bls12_381_G2_scalarMul/mulperiodic1"
     , "bls12_381_G2_scalarMul/mulperiodic2"
     , "bls12_381_G2_scalarMul/mulperiodic3"
     , "bls12_381_G2_scalarMul/mulperiodic4"
     , "bls12_381_G2_neg/neg"
     , "bls12_381_G2_neg/add-neg"
     , "bls12_381_G2_neg/neg-zero"
     , "bls12_381_G2_uncompress/zero"
     -- , "bls12_381_G2_uncompress/on-curve-serialised-not-compressed"
     -- , "bls12_381_G2_uncompress/off-curve"
     -- , "bls12_381_G2_uncompress/bad-zero-1"
     , "bls12_381_G2_uncompress/on-curve-bit3-set"
     -- , "bls12_381_G2_uncompress/too-short"
     -- , "bls12_381_G2_uncompress/out-of-group"
     , "bls12_381_G2_uncompress/on-curve-bit3-clear"
     -- , "bls12_381_G2_uncompress/too-long"
     -- , "bls12_381_G2_uncompress/bad-zero-2"
     -- , "bls12_381_G2_uncompress/bad-zero-3"
     , "bls12_381_millerLoop/random-pairing"
     , "bls12_381_millerLoop/balanced"
     , "bls12_381_millerLoop/equal-pairing"
     , "bls12_381_millerLoop/right-additive"
     , "bls12_381_millerLoop/left-additive"
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

