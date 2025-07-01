{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Name.Unique

import Data.Hashable

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , CaseBuiltin uni
  , GEq uni
  , Closed uni
  , Everywhere uni Eq
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
