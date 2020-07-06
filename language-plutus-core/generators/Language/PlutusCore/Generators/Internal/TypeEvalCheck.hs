-- | This module defines types and functions related to "type-eval checking".

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Generators.Internal.TypeEvalCheck
    ( TypeEvalCheckError (..)
    , TypeEvalCheckResult (..)
    , TypeEvalCheckM
    , typeEvalCheckBy
    , unsafeTypeEvalCheck
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Generators.Internal.TypedBuiltinGen
import           Language.PlutusCore.Generators.Internal.Utils

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck
import           Language.PlutusCore.Universe

import           Control.Lens.TH
import           Control.Monad.Except
import           Data.String
import           Data.Text.Prettyprint.Doc

{- Note [Type-eval checking]
We generate terms along with values they are supposed to evaluate to. Before evaluating a term,
we type check it. Then we evaluate the term and check whether the expected result matches with
the actual one. Thus "type-eval checking".
-}

-- | The type of errors that can occur during type-eval checking.
data TypeEvalCheckError uni
    = TypeEvalCheckErrorIllFormed (Error uni ())
    | TypeEvalCheckErrorException String
    | TypeEvalCheckErrorIllEvaled
          (EvaluationResult (Term TyName Name uni ()))
          (EvaluationResult (Term TyName Name uni ()))
      -- ^ The former is an expected result of evaluation, the latter -- is an actual one.
makeClassyPrisms ''TypeEvalCheckError

instance ann ~ () => AsError (TypeEvalCheckError uni) uni ann where
    _Error = _TypeEvalCheckErrorIllFormed . _Error

instance ann ~ () => AsTypeError (TypeEvalCheckError uni) uni ann where
    _TypeError = _TypeEvalCheckErrorIllFormed . _TypeError

-- | Type-eval checking of a term results in a value of this type.
data TypeEvalCheckResult uni = TypeEvalCheckResult
    { _termCheckResultType  :: Normalized (Type TyName uni ())
      -- ^ The type of the term.
    , _termCheckResultValue :: EvaluationResult (Term TyName Name uni ())
      -- ^ The result of evaluation of the term.
    }

instance (PrettyBy config (Error uni ()), PrettyBy config (Plain Term uni)) =>
        PrettyBy config (TypeEvalCheckError uni) where
    prettyBy config (TypeEvalCheckErrorIllFormed err)             =
        "The term is ill-formed:" <+> prettyBy config err
    prettyBy _      (TypeEvalCheckErrorException err)             =
        "An exception occurred:" <+> fromString err
    prettyBy config (TypeEvalCheckErrorIllEvaled expected actual) =
        "The expected value:" <+> prettyBy config expected <> hardline <>
        "doesn't match with the actual value:" <+> prettyBy config actual

-- | The monad type-eval checking runs in.
type TypeEvalCheckM uni = Either (TypeEvalCheckError uni)

-- See Note [Type-eval checking].
-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
typeEvalCheckBy
    :: ( KnownType (Term TyName Name uni ()) a, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` Eq, Pretty internal, PrettyPlc termErr
       )
    => (Plain Term uni -> Either (EvaluationException internal user termErr) (Plain Term uni))
       -- ^ An evaluator.
    -> TermOf uni a
    -> TypeEvalCheckM uni (TermOf uni (TypeEvalCheckResult uni))
typeEvalCheckBy eval (TermOf term x) = TermOf term <$> do
    termTy <- runQuoteT $ inferType defConfig term
    let valExpected = makeKnown x
    fmap (TypeEvalCheckResult termTy) $ case extractEvaluationResult (eval term) of
        Right valActual
            | valExpected == valActual -> return valActual
            | otherwise                ->
                throwError $ TypeEvalCheckErrorIllEvaled valExpected valActual
        Left exc -> throwError $ TypeEvalCheckErrorException $ show exc

-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
-- Throw an error in case something goes wrong.
unsafeTypeEvalCheck
    :: ( KnownType (Term TyName Name uni ()) a, GShow uni, GEq uni, DefaultUni <: uni, Closed uni
       , uni `EverywhereAll` [Eq, PrettyConst, ExMemoryUsage]
       )
    => TermOf uni a -> TermOf uni (EvaluationResult (Term TyName Name uni ()))
unsafeTypeEvalCheck termOfTbv = do
    let errOrRes = typeEvalCheckBy (evaluateCek mempty defaultCostModel) termOfTbv
    case errOrRes of
        Left err         -> error $ concat
            [ prettyPlcErrorString err
            , "\nin\n"
            , render . prettyPlcClassicDebug $ _termOfTerm termOfTbv
            ]
        Right termOfTecr -> _termCheckResultValue <$> termOfTecr
