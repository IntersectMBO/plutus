-- | A "classic" (i.e. as seen in the specification) way to pretty-print Untyped Plutus Core terms.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Core.Instance.Pretty.Classic () where

import PlutusPrelude

import UntypedPlutusCore.Core.Type

import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.PrettyConst

import Prettyprinter
import Prettyprinter.Custom
import Universe (Some (..), SomeTypeIn (SomeTypeIn), ValueOf (..))

instance (PrettyClassicBy configName name, PrettyUni uni, Pretty fun, Pretty ann) =>
        PrettyBy (PrettyConfigClassic configName) (Term name uni fun ann) where
    prettyBy config = \case
        Var ann n ->
            sep (consAnnIf config ann [prettyBy config n])
        LamAbs ann n t ->
            sexp "lam" (consAnnIf config ann
                [prettyBy config n, prettyBy config t])
        Apply ann t1 t2 ->
            brackets' (sep (consAnnIf config ann
                [prettyBy config t1, prettyBy config t2]))
        Constant ann c ->
            sexp "con" (consAnnIf config ann [prettyTypeOf c, pretty c])
        Builtin ann bi ->
            sexp "builtin" (consAnnIf config ann
                [pretty bi])
        Error ann ->
            sexp "error" (consAnnIf config ann [])
        Delay ann term ->
            sexp "delay" (consAnnIf config ann
                [prettyBy config term])
        Force ann term ->
            sexp "force" (consAnnIf config ann
                [prettyBy config term])
        Constr ann i es ->
            sexp "constr" (consAnnIf config ann (pretty i : fmap (prettyBy config) es))
        Case ann arg cs ->
            sexp "case" (consAnnIf config ann
                (prettyBy config arg : fmap (prettyBy config) (toList cs)))
        Let ann names body ->
          sexp "let" (consAnnIf config ann
              [ parens' (sep $ prettyBy config <$> names)
              , prettyBy config body
              ])
        Bind ann t binds ->
          sexp "bind" (consAnnIf config ann
              (prettyBy config t : (prettyBy config <$> binds)))
      where
        prettyTypeOf :: Some (ValueOf uni) -> Doc dann
        prettyTypeOf (Some (ValueOf uni _ )) = prettyBy juxtRenderContext $ SomeTypeIn uni

instance (PrettyClassicBy configName (Term name uni fun ann), Pretty ann) =>
        PrettyBy (PrettyConfigClassic configName) (Program name uni fun ann) where
    prettyBy config (Program ann version term) =
        sexp "program" (consAnnIf config ann [pretty version, prettyBy config term])
