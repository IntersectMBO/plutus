-- | This module defines types and functions related to "type-eval checking".

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Generators.Internal.TypeEvalCheck
    ( TypeEvalCheckError (..)
    , TypeEvalCheckResult (..)
    , TypeEvalCheckM
    , typeEvalCheckBy
    , unsafeTypeEvalCheck
    ) where

import qualified Language.PlutusCore.Check.ValueRestriction              as VR
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Generators.Internal.TypedBuiltinGen
import           Language.PlutusCore.Generators.Internal.Utils
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeCheck
import           PlutusPrelude

import           Control.Lens.TH
import           Control.Monad.Except
import           Data.Traversable

{- Note [Type-eval checking]
We generate terms along with values they are supposed to evaluate to. Before evaluating a term,
we type check it. Then we evaluate the term and check whether the expected result matches with
the actual one. Thus "type-eval checking".
-}

-- | The type of errors that can occur during type-eval checking.
data TypeEvalCheckError
    = TypeEvalCheckErrorIllFormed (Error ())
    | TypeEvalCheckErrorIllEvaled (Value TyName Name ()) (Value TyName Name ())
      -- ^ The former is an expected result of evaluation, the latter -- is an actual one.
makeClassyPrisms ''TypeEvalCheckError

instance ann ~ () => AsError TypeEvalCheckError ann where
    _Error = _TypeEvalCheckErrorIllFormed . _Error

instance (tyname ~ TyName, ann ~ ()) => AsValueRestrictionError TypeEvalCheckError tyname ann where
    _ValueRestrictionError = _TypeEvalCheckErrorIllFormed . _ValueRestrictionError

instance ann ~ () => AsTypeError TypeEvalCheckError ann where
    _TypeError = _TypeEvalCheckErrorIllFormed . _TypeError

-- | Type-eval checking of a term results in a value of this type.
data TypeEvalCheckResult = TypeEvalCheckResult
    { _termCheckResultType  :: NormalizedType TyName ()
      -- ^ The type of the term.
    , _termCheckResultValue :: EvaluationResult
      -- ^ The result of evaluation of the term.
    }

instance (PrettyBy config (Error ()), PrettyBy config (Value TyName Name ())) =>
        PrettyBy config TypeEvalCheckError where
    prettyBy config (TypeEvalCheckErrorIllFormed err)             =
        "The term is ill-formed:" <+> prettyBy config err
    prettyBy config (TypeEvalCheckErrorIllEvaled expected actual) =
        "The expected value:" <+> prettyBy config expected <> hardline <>
        "doesn't match with the actual value:" <+> prettyBy config actual

-- | The monad type-eval checking runs in.
type TypeEvalCheckM = Either TypeEvalCheckError

-- See Note [Type-eval checking].
-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
typeEvalCheckBy
    :: (Term TyName Name () -> EvaluationResult) -- ^ An evaluator.
    -> TermOf (TypedBuiltinValue Size a)
    -> TypeEvalCheckM (TermOf TypeEvalCheckResult)
typeEvalCheckBy eval (TermOf term tbv) = TermOf term <$> do
    _ <- VR.checkTerm term
    termTy <- runQuoteT $ inferType defOffChainConfig term
    let resExpected = maybeToEvaluationResult $ makeBuiltin tbv
    fmap (TypeEvalCheckResult termTy) $
        for ((,) <$> resExpected <*> eval term) $ \(valExpected, valActual) ->
            if valExpected == valActual
                then return valActual
                else throwError $ TypeEvalCheckErrorIllEvaled valExpected valActual

-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
-- Throw an error in case something goes wrong.
unsafeTypeEvalCheck
    :: forall a. TermOf (TypedBuiltinValue Size a) -> Maybe (TermOf (Value TyName Name ()))
unsafeTypeEvalCheck termOfTbv = do
    let errOrRes = typeEvalCheckBy evaluateCk termOfTbv
    case errOrRes of
        Left err         -> errorPlc err
        Right termOfTecr -> traverse (evaluationResultToMaybe . _termCheckResultValue) termOfTecr
