module Language.PlutusCore.Generators.Test
    ( propEvaluate
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Generators

import           Control.Monad.Morph
import           Data.Foldable
import           Hedgehog                              hiding (Size, Var, eval)

-- TODO: also type check the terms.
-- | A property-based testing procedure for evaluators.
-- Checks whether a term generated along with the value it's supposed to compute to
-- indeed computes to that value according to the provided evaluate.
propEvaluate
    :: (Term TyName Name () -> EvaluationResult)       -- ^ An evaluator.
    -> GenT Quote (TermOf (TypedBuiltinValue Size a))  -- ^ A term/value generator.
    -> Property
propEvaluate eval genTermOfTbv = property . hoist (return . runQuote) $ do
    TermOf term tbv <- forAllPrettyCfgT genTermOfTbv
    resExpected <- lift $ unsafeMakeBuiltin tbv
    for_ (evaluationResultToMaybe $ eval term) $ \resActual ->
        resActual === resExpected
