-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Core.Instance.Pretty.Classic () where

import           PlutusPrelude

import           PlutusCore.Core.Instance.Pretty.Common ()
import           PlutusCore.Core.Type
import           PlutusCore.Pretty.Classic
import           PlutusCore.Pretty.PrettyConst

import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Custom
import           Universe

instance Pretty ann => PrettyBy (PrettyConfigClassic configName) (Kind ann) where
    prettyBy config = \case
        Type ann           ->
            parens (vsep' (consAnnIf config ann
                ["type"]))
        KindArrow ann k k' ->
            parens ("fun" </> vsep' (consAnnIf config ann
                [prettyBy config k, prettyBy config k']))

instance (PrettyClassicBy configName tyname, GShow uni, Pretty ann) =>
        PrettyBy (PrettyConfigClassic configName) (Type tyname uni ann) where
    prettyBy config = \case
        TyApp ann t t'     ->
            brackets' (vsep' (consAnnIf config ann
                [prettyBy config t, prettyBy config t']))
        TyVar ann n        ->
            vsep' (consAnnIf config ann
                [prettyBy config n])
        TyFun ann t t'     ->
            parens ("fun" </> vsep' (consAnnIf config ann
                [prettyBy config t, prettyBy config t']))
        TyIFix ann pat arg ->
            parens ("ifix" </> vsep' (consAnnIf config ann
                [prettyBy config pat, prettyBy config arg]))
        TyForall ann n k t ->
            parens ("all" </> vsep' (consAnnIf config ann
                [prettyBy config n, prettyBy config k, prettyBy config t]))
        TyBuiltin ann n    ->
            parens ("con" </> vsep' (consAnnIf config ann
                [pretty n]))
        TyLam ann n k t    ->
            parens ("lam" </> vsep' (consAnnIf config ann
                [prettyBy config n, prettyBy config k, prettyBy config t]))

instance
        ( PrettyClassicBy configName tyname
        , PrettyClassicBy configName name
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun
        , Pretty ann
        ) => PrettyBy (PrettyConfigClassic configName) (Term tyname name uni fun ann) where
    prettyBy config = \case
        Var ann n ->
            vsep' (consAnnIf config ann [prettyBy config n])
        TyAbs ann tn k t ->
            parens' ("abs" </> vsep' (consAnnIf config ann
                [prettyBy config tn, prettyBy config k, prettyBy config t]))
        LamAbs ann n ty t ->
            parens' ("lam" </> vsep' (consAnnIf config ann
                [prettyBy config n, prettyBy config ty, prettyBy config t]))
        Apply ann t1 t2 ->
            brackets' (vsep' (consAnnIf config ann
                [prettyBy config t1, prettyBy config t2]))
        Constant ann c ->
            parens' ("con" </> vsep' (consAnnIf config ann [prettyTypeOf c]) </> pretty c)
        Builtin ann bi ->
            parens' ("builtin" </> vsep' (consAnnIf config ann
                [pretty bi]))
        TyInst ann t ty ->
            braces' (vsep' (consAnnIf config ann
                [prettyBy config t, prettyBy config ty]))
        Error ann ty ->
            parens' ("error" </> vsep' (consAnnIf config ann
                [prettyBy config ty]))
        IWrap ann ty1 ty2 t ->
            parens' ("iwrap" </> vsep' (consAnnIf config ann
                [prettyBy config ty1, prettyBy config ty2, prettyBy config t]))
        Unwrap ann t ->
            parens' ("unwrap" </> vsep' (consAnnIf config ann
                [prettyBy config t]))
      where
        prettyTypeOf :: GShow t => Some (ValueOf t) -> Doc dann
        prettyTypeOf (Some (ValueOf uni _ )) = pretty $ SomeTypeIn uni

instance (PrettyClassicBy configName (Term tyname name uni fun ann), Pretty ann) =>
        PrettyBy (PrettyConfigClassic configName) (Program tyname name uni fun ann) where
    prettyBy config (Program ann version term) =
        parens' $ "program" <+> vsep' (consAnnIf config ann [pretty version]) <//> prettyBy config term
