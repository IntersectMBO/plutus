{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import Data.Hashable
import PlutusCore.Builtin
import PlutusCore.Name.Unique
import PlutusCore.Quote

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
