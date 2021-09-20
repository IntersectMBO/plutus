-- | A "classic" (i.e. as seen in the specification) way to pretty-print Untyped Plutus Core terms.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Core.Instance.Pretty.Classic () where

import           PlutusPrelude

import           UntypedPlutusCore.Core.Type

import           PlutusCore.Core.Instance.Pretty.Common ()
import           PlutusCore.Pretty.Classic
import           PlutusCore.Pretty.PrettyConst

import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Custom
import           Universe

instance
        ( PrettyClassicBy configName name
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun
        , Pretty ann
        ) => PrettyBy (PrettyConfigClassic configName) (Term name uni fun ann) where
    prettyBy config = \case
        Var ann n ->
            vsep' (consAnnIf config ann [prettyBy config n])
        LamAbs ann n t ->
            parens' ("lam" </> vsep' (consAnnIf config ann
                [prettyBy config n, prettyBy config t]))
        Apply ann t1 t2 ->
            brackets' (vsep' (consAnnIf config ann
                [prettyBy config t1, prettyBy config t2]))
        Constant ann c ->
            parens' ("con" </> vsep' (consAnnIf config ann [prettyTypeOf c]) </> pretty c)
        Builtin ann bi ->
            parens' ("builtin" </> vsep' (consAnnIf config ann
                [pretty bi]))
        Error ann ->
            parens' ("error" <> vsep' (consAnnIf config ann []))
        Delay ann term ->
            parens' ("delay" </> vsep' (consAnnIf config ann
                [prettyBy config term]))
        Force ann term ->
            parens' ("force" </> vsep' (consAnnIf config ann
                [prettyBy config term]))
      where
        prettyTypeOf :: GShow t => Some (ValueOf t) -> Doc dann
        prettyTypeOf (Some (ValueOf uni _ )) = pretty $ SomeTypeIn uni

instance (PrettyClassicBy configName (Term name uni fun ann), Pretty ann) =>
        PrettyBy (PrettyConfigClassic configName) (Program name uni fun ann) where
    prettyBy config (Program ann version term) =
        parens' $ "program" <+> vsep' (consAnnIf config ann [pretty version]) <//> prettyBy config term
