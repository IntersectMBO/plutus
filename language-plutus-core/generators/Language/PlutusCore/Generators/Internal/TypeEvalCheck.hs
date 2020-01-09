-- | This module defines types and functions related to "type-eval checking".

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Generators.Internal.TypeEvalCheck
    ( TypeEvalCheckError (..)
    , TypeEvalCheckResult (..)
    , TypeEvalCheckM
    , typeEvalCheckBy
    , unsafeTypeEvalCheck
    ) where

import           PlutusPrelude

import           PlcTestUtils

import           Language.PlutusCore.Generators.Internal.TypedBuiltinGen
import           Language.PlutusCore.Generators.Internal.Utils

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck

import           Control.Lens.TH
import           Control.Monad.Except
import           Data.String

{- Note [Type-eval checking]
We generate terms along with values they are supposed to evaluate to. Before evaluating a term,
we type check it. Then we evaluate the term and check whether the expected result matches with
the actual one. Thus "type-eval checking".
-}

-- | The type of errors that can occur during type-eval checking.
data TypeEvalCheckError
    = TypeEvalCheckErrorIllFormed (Error ())
    | TypeEvalCheckErrorException String
    | TypeEvalCheckErrorIllEvaled EvaluationResultDef EvaluationResultDef
      -- ^ The former is an expected result of evaluation, the latter -- is an actual one.
makeClassyPrisms ''TypeEvalCheckError

instance ann ~ () => AsError TypeEvalCheckError ann where
    _Error = _TypeEvalCheckErrorIllFormed . _Error

instance ann ~ () => AsTypeError TypeEvalCheckError ann where
    _TypeError = _TypeEvalCheckErrorIllFormed . _TypeError

-- | Type-eval checking of a term results in a value of this type.
data TypeEvalCheckResult = TypeEvalCheckResult
    { _termCheckResultType  :: Normalized (Type TyName ())
      -- ^ The type of the term.
    , _termCheckResultValue :: EvaluationResultDef
      -- ^ The result of evaluation of the term.
    }

instance (PrettyBy config (Error ()), PrettyBy config (Value TyName Name ())) =>
        PrettyBy config TypeEvalCheckError where
    prettyBy config (TypeEvalCheckErrorIllFormed err)             =
        "The term is ill-formed:" <+> prettyBy config err
    prettyBy _      (TypeEvalCheckErrorException err)             =
        "An exception occurred:" <+> fromString err
    prettyBy config (TypeEvalCheckErrorIllEvaled expected actual) =
        "The expected value:" <+> prettyBy config expected <> hardline <>
        "doesn't match with the actual value:" <+> prettyBy config actual

-- | The monad type-eval checking runs in.
type TypeEvalCheckM = Either TypeEvalCheckError

-- See Note [Type-eval checking].
-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
typeEvalCheckBy
    :: (Pretty err, KnownType a)
    => (Term TyName Name () -> Either (MachineException err) EvaluationResultDef)
       -- ^ An evaluator.
    -> TermOf a
    -> TypeEvalCheckM (TermOf TypeEvalCheckResult)
typeEvalCheckBy eval (TermOf term x) = TermOf term <$> do
    termTy <- runQuoteT $ inferType defOffChainConfig term
    let valExpected = case makeKnown x of
            Error _ _ -> EvaluationFailure
            t         -> EvaluationSuccess t
    fmap (TypeEvalCheckResult termTy) $ case eval term of
        Right valActual
            | valExpected == valActual -> return valActual
            | otherwise                ->
                throwError $ TypeEvalCheckErrorIllEvaled valExpected valActual
        Left exc -> throwError $ TypeEvalCheckErrorException $ show exc

-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
-- Throw an error in case something goes wrong.
unsafeTypeEvalCheck
    :: forall a. KnownType a => TermOf a -> TermOf EvaluationResultDef
unsafeTypeEvalCheck termOfTbv = do
    let errOrRes = typeEvalCheckBy (pureTry @CkMachineException . evaluateCk) termOfTbv
    case errOrRes of
        Left err         -> error $ concat
            [ prettyPlcErrorString err
            , "\nin\n"
            , docString . prettyPlcClassicDebug $ _termOfTerm termOfTbv
            ]
        Right termOfTecr -> _termCheckResultValue <$> termOfTecr
