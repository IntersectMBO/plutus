module Language.PlutusCore.Evaluation.Evaluator
    ( AnEvaluator
    , Evaluator
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

-- | A thing that evaluates @f@ to @a@ in monad @m@ in an environment of built-in functions.
type AnEvaluator f uni m a = DynamicBuiltinNameMeanings uni -> f TyName Name uni () -> m a

-- | A thing that evaluates @f@ to 'Term' in monad @m@ and an environment of built-in functions.
type Evaluator f uni m = AnEvaluator f uni m (Term TyName Name uni ())
