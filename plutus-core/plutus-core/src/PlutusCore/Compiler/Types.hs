{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import PlutusCore.Builtin
import PlutusCore.Name.Unique
import PlutusCore.Quote

import Data.Hashable

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
