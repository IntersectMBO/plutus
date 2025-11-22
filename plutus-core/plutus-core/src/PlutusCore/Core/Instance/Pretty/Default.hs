{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| While the flexible pretty-printing infrastructure is useful when you want it,
it's helpful to have an implementation of the default Pretty typeclass that
does the default thing. -}
module PlutusCore.Core.Instance.Pretty.Default () where

import PlutusPrelude

import PlutusCore.Core.Instance.Pretty.Classic ()
import PlutusCore.Core.Type
import PlutusCore.Name.Unique
import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.PrettyConst

import Universe

instance Pretty TyName where
  pretty = prettyClassic

instance Pretty Name where
  pretty = prettyClassic

instance Pretty ann => Pretty (Kind ann) where
  pretty = prettyClassic

instance
  (PrettyClassic tyname, PrettyParens (SomeTypeIn uni), Pretty ann)
  => Pretty (Type tyname uni ann)
  where
  pretty = prettyClassic

instance
  ( PrettyClassic tyname
  , PrettyClassic name
  , PrettyUni uni
  , Pretty fun
  , Pretty ann
  )
  => Pretty (Term tyname name uni fun ann)
  where
  pretty = prettyClassic

instance
  ( PrettyClassic tyname
  , PrettyClassic name
  , PrettyUni uni
  , Pretty fun
  , Pretty ann
  )
  => Pretty (Program tyname name uni fun ann)
  where
  pretty = prettyClassic
