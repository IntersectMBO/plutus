{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Evaluation.ErrorWithCause
  ( ErrorWithCause (..)
  , throwErrorWithCause
  ) where

import PlutusPrelude

import PlutusCore.Pretty

import Control.Monad.Except
import Data.Bifunctor
import Prettyprinter

-- | An error and (optionally) what caused it.
data ErrorWithCause err cause = ErrorWithCause
  { _ewcError :: !err
  , _ewcCause :: !(Maybe cause)
  }
  deriving stock (Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

instance Bifunctor ErrorWithCause where
  bimap f g (ErrorWithCause err cause) = ErrorWithCause (f err) (g <$> cause)
  {-# INLINE bimap #-}

instance (Pretty err, Pretty cause) => Pretty (ErrorWithCause err cause) where
  pretty (ErrorWithCause e c) = pretty e <+> "caused by:" <+> pretty c

instance
  (PrettyBy config cause, PrettyBy config err)
  => PrettyBy config (ErrorWithCause err cause)
  where
  prettyBy config (ErrorWithCause err mayCause) =
    fold
      [ "An error has occurred:"
      , hardline
      , prettyBy config err
      , case mayCause of
          Nothing -> mempty
          Just cause -> hardline <> "Caused by:" <+> prettyBy config cause
      ]

instance
  (PrettyPlc cause, PrettyPlc err)
  => Show (ErrorWithCause err cause)
  where
  show = render . prettyPlcReadable

deriving anyclass instance
  (PrettyPlc cause, PrettyPlc err, Typeable cause, Typeable err)
  => Exception (ErrorWithCause err cause)

throwErrorWithCause
  :: MonadError (ErrorWithCause e cause) m
  => e
  -> cause
  -> m x
throwErrorWithCause e = throwError . ErrorWithCause e . Just
{-# INLINE throwErrorWithCause #-}
