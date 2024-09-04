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

1. Structural ones -- these are errors that are indicative of the _structure_ of the program being
   wrong. For example, a free variable was encountered during evaluation, a non-function was
   applied to an argument or 'tailList' was applied to a non-list.
2. Operational ones -- these are errors that are indicative of the _logic_ of the program being
   wrong. For example, 'error' was executed, 'tailList' was applied to an empty list or evaluation
   ran out of gas.

On the chain both of these are just regular failures and we don't distinguish between them there:
if a script fails, it fails, it doesn't matter what the reason was. However in the tests it does
matter why the failure occurred: a structural error may indicate that the test was written
incorrectly while an operational error may be entirely expected.

In other words, structural errors are \"runtime type errors\" and operational errors are regular
runtime errors. Which means that evaluating an (erased) well-typed program should never produce a
structural error, only an operational one. This creates a sort of \"runtime type system\" for UPLC
and it would be great to stick to it and enforce in tests etc, but we currently don't.
-}
data EvaluationError structural operational
    = StructuralEvaluationError !structural
    | OperationalEvaluationError !operational
    deriving stock (Show, Eq, Functor, Generic)
    deriving anyclass (NFData)

mtraverse makeClassyPrisms
    [ ''EvaluationError
    ]

instance Bifunctor EvaluationError where
    bimap f _ (StructuralEvaluationError err)  = StructuralEvaluationError $ f err
    bimap _ g (OperationalEvaluationError err) = OperationalEvaluationError $ g err
    {-# INLINE bimap #-}

instance Bifoldable EvaluationError where
    bifoldMap f _ (StructuralEvaluationError err)  = f err
    bifoldMap _ g (OperationalEvaluationError err) = g err
    {-# INLINE bifoldMap #-}

instance Bitraversable EvaluationError where
    bitraverse f _ (StructuralEvaluationError err)  = StructuralEvaluationError <$> f err
    bitraverse _ g (OperationalEvaluationError err) = OperationalEvaluationError <$> g err
    {-# INLINE bitraverse #-}

-- | A raw evaluation failure is always an operational error.
instance AsEvaluationFailure operational =>
        AsEvaluationFailure (EvaluationError structural operational) where
    _EvaluationFailure = _OperationalEvaluationError . _EvaluationFailure
    {-# INLINE _EvaluationFailure #-}

instance
        ( HasPrettyDefaults config ~ 'True
        , PrettyBy config structural, Pretty operational
        ) => PrettyBy config (EvaluationError structural operational) where
    prettyBy config (StructuralEvaluationError structural)   = prettyBy config structural
    prettyBy _      (OperationalEvaluationError operational) = pretty operational

instance (Pretty structural, Pretty operational) =>
        Pretty (EvaluationError structural operational) where
    pretty (StructuralEvaluationError structural)   = pretty structural
    pretty (OperationalEvaluationError operational) = pretty operational
