-- | Various views of PLC entities.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.PlutusCore.View
    ( IterApp(..)
    , TermIterApp
    , termAsTermIterApp
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core

import           Data.Text.Prettyprint.Doc

-- | A function (called "head") applied to a list of arguments (called "spine").
data IterApp head arg = IterApp
    { _iterAppHead  :: head
    , _iterAppSpine :: [arg]
    }

-- | An iterated application of a 'Term' to a list of 'Term's.
type TermIterApp tyname name uni a =
    IterApp (Term tyname name uni a) (Term tyname name uni a)

instance (PrettyBy config head, PrettyBy config arg) => PrettyBy config (IterApp head arg) where
    prettyBy config (IterApp appHead appSpine) =
        parens $ foldl' (\fun arg -> fun <+> prettyBy config arg) (prettyBy config appHead) appSpine

-- | An iterated application of a 'Term' to a list of 'Term's.
termAsTermIterApp :: Term tyname name uni a -> TermIterApp tyname name uni a
termAsTermIterApp = go [] where
    go args (Apply _ fun arg) = go (arg : args) fun
    go args (TyInst _ fun _)  = go args fun
    go args  fun              = IterApp fun args
