{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import Data.Hashable
import PlutusCore.Builtin
import PlutusCore.Name.Unique
import PlutusCore.Quote
import UntypedPlutusCore.Core.Type (Term)

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , CaseBuiltin (Term name uni fun a) uni
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
