{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| While the flexible pretty-printing infrastructure is useful when you want it,
it's helpful to have an implementation of the default Pretty typeclass that
does the default thing. -}
module UntypedPlutusCore.Core.Instance.Pretty.Default () where

import PlutusPrelude

import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.PrettyConst

import UntypedPlutusCore.Core.Instance.Pretty.Classic ()
import UntypedPlutusCore.Core.Type

instance
  (PrettyClassic name, PrettyUni uni, Pretty fun, Pretty ann)
  => Pretty (Term name uni fun ann)
  where
  pretty = prettyClassic

instance
  (PrettyClassic name, PrettyUni uni, Pretty fun, Pretty ann)
  => Pretty (Program name uni fun ann)
  where
  pretty = prettyClassic
