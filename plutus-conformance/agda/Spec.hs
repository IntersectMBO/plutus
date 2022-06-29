{- | Conformance tests for the Agda implementation. -}

module Main (main) where

import Control.Monad.Error.Class
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
agdaEvalUplcProg p =
    let
        -- turn a UPLC program to a UPLC term
        tmU = UPLC.progTerm p
        -- turn it into an untyped de Bruijn term
        tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
        tmUDB = deBruijnTerm tmU
    in
    case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
        -- if there's an exception, evaluation failed, should return `Nothing`.
        Left _ -> Nothing
        -- evaluate the untyped term with CEK
        Right tmUDBSuccess ->
            case liftEither $ runUAgda tmUDBSuccess of
                Left _ -> Nothing
                Right tmEvaluated ->
                    -- turn it back into a named term
                    case runQuote $ runExceptT $ withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated of
                        Left _          -> Nothing
                        Right namedTerm -> Just $ UPLC.mkDefaultProg namedTerm

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg

