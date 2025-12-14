{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- editorconfig-checker-disable-file
-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- | The exceptions that an abstract machine can throw.
module PlutusCore.Evaluation.Error
  ( EvaluationError (..)
  ) where

import PlutusPrelude

import Control.Lens
import Data.Bifoldable
import Data.Bitraversable

{-| The type of errors that can occur during evaluation. There are two kinds of errors:

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
and it would be great to stick to it and enforce in tests etc, but we currently don't. -}
data EvaluationError structural operational
  = StructuralError !structural
  | OperationalError !operational
  deriving stock (Show, Eq, Functor, Generic)
  deriving anyclass (NFData)

instance Bifunctor EvaluationError where
  bimap f _ (StructuralError err) = StructuralError $ f err
  bimap _ g (OperationalError err) = OperationalError $ g err
  {-# INLINE bimap #-}

instance Bifoldable EvaluationError where
  bifoldMap f _ (StructuralError err) = f err
  bifoldMap _ g (OperationalError err) = g err
  {-# INLINE bifoldMap #-}

instance Bitraversable EvaluationError where
  bitraverse f _ (StructuralError err) = StructuralError <$> f err
  bitraverse _ g (OperationalError err) = OperationalError <$> g err
  {-# INLINE bitraverse #-}

instance
  ( HasPrettyDefaults config ~ 'True
  , PrettyBy config structural
  , Pretty operational
  )
  => PrettyBy config (EvaluationError structural operational)
  where
  prettyBy config (StructuralError structural) = prettyBy config structural
  prettyBy _ (OperationalError operational) = pretty operational

instance
  (Pretty structural, Pretty operational)
  => Pretty (EvaluationError structural operational)
  where
  pretty (StructuralError structural) = pretty structural
  pretty (OperationalError operational) = pretty operational
