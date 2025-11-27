-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines types and functions related to "type-eval checking".
module PlutusCore.Generators.Hedgehog.TypeEvalCheck
  ( TypeEvalCheckError (..)
  , TypeEvalCheckResult (..)
  , TypeEvalCheckM
  , typeEvalCheckBy
  , unsafeTypeEvalCheck
  ) where

import PlutusPrelude

import PlutusCore.Generators.Hedgehog.TypedBuiltinGen
import PlutusCore.Generators.Hedgehog.Utils

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Normalize
import PlutusCore.Pretty

import Control.Monad.Except
import Data.Proxy
import Data.String
import Prettyprinter

{- Note [Type-eval checking]
We generate terms along with values they are supposed to evaluate to. Before evaluating a term,
we type check it. Then we evaluate the term and check whether the expected result matches with
the actual one. Thus "type-eval checking".
-}

-- | The type of errors that can occur during type-eval checking.
data TypeEvalCheckError uni fun
  = TypeEvalCheckErrorIllFormed !(Error uni fun ())
  | TypeEvalCheckErrorIllTyped
      !(Normalized (Type TyName uni ()))
      !(Normalized (Type TyName uni ()))
  | TypeEvalCheckErrorException !String
  | -- | The former is an expected result of evaluation, the latter -- is an actual one.
    TypeEvalCheckErrorIllEvaled
      !(EvaluationResult (Term TyName Name uni fun ()))
      !(EvaluationResult (Term TyName Name uni fun ()))

-- | Type-eval checking of a term results in a value of this type.
data TypeEvalCheckResult uni fun = TypeEvalCheckResult
  { _termCheckResultType :: Normalized (Type TyName uni ())
  -- ^ The type of the term.
  , _termCheckResultValue :: EvaluationResult (Term TyName Name uni fun ())
  -- ^ The result of evaluation of the term.
  }

instance
  ( PrettyBy config (Type TyName uni ())
  , PrettyBy config (Term TyName Name uni fun ())
  , PrettyBy config (Error uni fun ())
  )
  => PrettyBy config (TypeEvalCheckError uni fun)
  where
  prettyBy config (TypeEvalCheckErrorIllFormed err) =
    "The term is ill-formed:" <+> prettyBy config err
  prettyBy config (TypeEvalCheckErrorIllTyped expected actual) =
    "The expected type:"
      <+> prettyBy config expected
      <> hardline
      <> "doesn't match with the actual type:"
      <+> prettyBy config actual
  prettyBy _ (TypeEvalCheckErrorException err) =
    "An exception occurred:" <+> fromString err
  prettyBy config (TypeEvalCheckErrorIllEvaled expected actual) =
    "The expected value:"
      <+> prettyBy config expected
      <> hardline
      <> "doesn't match with the actual value:"
      <+> prettyBy config actual

-- | The monad type-eval checking runs in.
type TypeEvalCheckM uni fun = Either (TypeEvalCheckError uni fun)

-- See Note [Type-eval checking].
-- | Type check and evaluate a term and check that the expected result is equal to the actual one.
typeEvalCheckBy
  :: ( uni ~ DefaultUni
     , fun ~ DefaultFun
     , KnownTypeAst TyName uni a
     , MakeKnown (Term TyName Name uni fun ()) a
     , PrettyPlc structural
     )
  => ( Term TyName Name uni fun ()
       -> Either
            (EvaluationException structural operational (Term TyName Name uni fun ()))
            (Term TyName Name uni fun ())
     )
  -- ^ An evaluator.
  -> TermOf (Term TyName Name uni fun ()) a
  -> TypeEvalCheckM uni fun (TermOf (Term TyName Name uni fun ()) (TypeEvalCheckResult uni fun))
typeEvalCheckBy eval (TermOf term (x :: a)) =
  TermOf term <$> do
    let tyExpected = runQuote . normalizeType $ toTypeAst (Proxy @a)
        valExpected = makeKnownOrFail x
    tyActual <- runQuoteT $ modifyError (TypeEvalCheckErrorIllFormed . TypeErrorE) $ do
      config <- getDefTypeCheckConfig ()
      inferType config term
    if tyExpected == tyActual
      then case splitStructuralOperational $ eval term of
        Right valActual ->
          if valExpected == valActual
            then return $ TypeEvalCheckResult tyExpected valActual
            else throwError $ TypeEvalCheckErrorIllEvaled valExpected valActual
        Left exc -> throwError $ TypeEvalCheckErrorException $ show exc
      else throwError $ TypeEvalCheckErrorIllTyped tyExpected tyActual

{-| Type check and evaluate a term and check that the expected result is equal to the actual one.
Throw an error in case something goes wrong. -}
unsafeTypeEvalCheck
  :: ( uni ~ DefaultUni
     , fun ~ DefaultFun
     , KnownTypeAst TyName uni a
     , MakeKnown (Term TyName Name uni fun ()) a
     )
  => TermOf (Term TyName Name uni fun ()) a
  -> TermOf (Term TyName Name uni fun ()) (EvaluationResult (Term TyName Name uni fun ()))
unsafeTypeEvalCheck termOfTbv = do
  let errOrRes = typeEvalCheckBy (evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def) termOfTbv
  case errOrRes of
    Left err ->
      error $
        concat
          [ prettyPlcErrorString err
          , "\nin\n"
          , render . prettyPlcClassicSimple $ _termOfTerm termOfTbv
          ]
    Right termOfTecr -> _termCheckResultValue <$> termOfTecr
