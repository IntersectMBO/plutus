{-# LANGUAGE KindSignatures #-}

module Language.PlutusCore.Evaluation.Evaluator
    ( AnEvaluator
    , Evaluator
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Name

-- | A thing that evaluates @f@ to @a@ in monad @m@ in an environment of built-in functions.
type AnEvaluator f (uni :: * -> *) (fun :: *) m a =
    DynamicBuiltinNameMeanings (WithMemory f uni fun) -> f TyName Name uni fun () -> m a

-- | A thing that evaluates @f@ to 'Term' in monad @m@ and an environment of built-in functions.
type Evaluator f uni fun m = AnEvaluator f uni fun m (WithMemory Term uni fun)
