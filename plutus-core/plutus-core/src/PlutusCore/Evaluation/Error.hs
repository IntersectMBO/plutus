-- editorconfig-checker-disable-file
-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Evaluation.Error
    ( EvaluationError (..)
    , AsEvaluationError (..)
    ) where

import PlutusPrelude

import PlutusCore.Evaluation.Result

import Control.Lens
import Data.Bifoldable
import Data.Bitraversable

{- | The type of errors that can occur during evaluation. There are two kinds of errors:

1. Operational ones -- these are errors that are indicative of the _logic_ of the program being
   wrong. For example, 'error' was executed, 'tailList' was applied to an empty list or evaluation
   ran out of gas.
2. Structural ones -- these are errors that are indicative of the _structure_ of the program being
   wrong. For example, a free variable was encountered during evaluation, a non-function was
   applied to an argument or 'tailList' was applied to a non-list.

On the chain both of these are just regular failures and we don't distinguish between them there:
if a script fails, it fails, it doesn't matter what the reason was. However in the tests it does
matter why the failure occurred: a structural error may indicate that the test was written
incorrectly while an operational error may be entirely expected.

In other words, operational errors are regular runtime errors and structural errors are \"runtime
type errors\". Which means that evaluating an (erased) well-typed program should never produce a
structural error, only an operational one. This creates a sort of \"runtime type system\" for UPLC
and it would be great to stick to it and enforce in tests etc, but we currently don't. For example,
a built-in function expecting a list but getting something else should throw a structural error,
but currently it'll throw an operational one. This is something that we plan to improve upon in
future.
-}
data EvaluationError operational structural
    = OperationalEvaluationError !operational
    | StructuralEvaluationError !structural
    deriving stock (Show, Eq, Functor, Generic)
    deriving anyclass (NFData)

mtraverse makeClassyPrisms
    [ ''EvaluationError
    ]

instance Bifunctor EvaluationError where
    bimap f _ (OperationalEvaluationError err) = OperationalEvaluationError $ f err
    bimap _ g (StructuralEvaluationError err)  = StructuralEvaluationError $ g err
    {-# INLINE bimap #-}

instance Bifoldable EvaluationError where
    bifoldMap f _ (OperationalEvaluationError err) = f err
    bifoldMap _ g (StructuralEvaluationError err)  = g err
    {-# INLINE bifoldMap #-}

instance Bitraversable EvaluationError where
    bitraverse f _ (OperationalEvaluationError err) = OperationalEvaluationError <$> f err
    bitraverse _ g (StructuralEvaluationError err)  = StructuralEvaluationError <$> g err
    {-# INLINE bitraverse #-}

-- | A raw evaluation failure is always an operational error.
instance AsEvaluationFailure operational =>
        AsEvaluationFailure (EvaluationError operational structural) where
    _EvaluationFailure = _OperationalEvaluationError . _EvaluationFailure
    {-# INLINE _EvaluationFailure #-}

instance
        ( HasPrettyDefaults config ~ 'True
        , Pretty operational, PrettyBy config structural
        ) => PrettyBy config (EvaluationError operational structural) where
    prettyBy _      (OperationalEvaluationError operational) = pretty operational
    prettyBy config (StructuralEvaluationError structural)   = prettyBy config structural

instance (Pretty operational, Pretty structural) =>
        Pretty (EvaluationError operational structural) where
    pretty (OperationalEvaluationError operational) = pretty operational
    pretty (StructuralEvaluationError structural)   = pretty structural
