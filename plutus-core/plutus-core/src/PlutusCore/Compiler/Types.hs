{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Name.Unique

import Data.Hashable

type Compiling m uni fun pat name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , CaseBuiltin uni
  , GEq uni
  , Closed uni
  , Everywhere uni Eq
  , Eq pat
  , Typeable pat
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  , Hashable pat
  )
