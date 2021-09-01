{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module PlutusIR.Core.Instance.Pretty () where

import           PlutusPrelude

import qualified PlutusCore                       as PLC
import           PlutusCore.Flat                  ()
import qualified PlutusCore.Pretty                as PLC

import           PlutusIR.Core.Type

import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Custom

-- Pretty-printing

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (VarDecl tyname name uni fun ann) where
    prettyBy config (VarDecl ann n ty) =
        sexp "vardecl" (PLC.consAnnIf config ann [prettyBy config n, prettyBy config ty])

instance ( PLC.PrettyClassicBy configName tyname
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (TyVarDecl tyname ann) where
    prettyBy config (TyVarDecl ann n ty) =
        sexp "tyvardecl" (PLC.consAnnIf config ann [prettyBy config n, prettyBy config ty])

instance PrettyBy (PLC.PrettyConfigClassic configName) Recursivity where
    prettyBy _ = \case
        NonRec -> parens "nonrec"
        Rec    -> parens "rec"

instance PrettyBy (PLC.PrettyConfigClassic configName) Strictness where
    prettyBy _ = \case
        NonStrict -> parens "nonstrict"
        Strict    -> parens "strict"

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Datatype tyname name uni fun ann) where
    prettyBy config (Datatype ann ty tyvars destr constrs) =
        sexp "datatype" (PLC.consAnnIf config ann
            [ prettyBy config ty
            , sep $ fmap (prettyBy config) tyvars
            , prettyBy config destr
            , sep $ fmap (prettyBy config) constrs
            ])

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Binding tyname name uni fun ann) where
    prettyBy config = \case
        TermBind ann s d t ->
            sexp "termbind" (PLC.consAnnIf config ann
                [prettyBy config s, prettyBy config d, prettyBy config t])
        TypeBind ann d ty  ->
            sexp "typebind" (PLC.consAnnIf config ann
                [prettyBy config d, prettyBy config ty])
        DatatypeBind ann d ->
            sexp "datatypebind" (PLC.consAnnIf config ann
                [prettyBy config d])

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Term tyname name uni fun ann) where
    prettyBy config = \case
        Let ann r bs t ->
            sexp "let" (PLC.consAnnIf config ann
                [prettyBy config r, sep . toList $ fmap (prettyBy config) bs, prettyBy config t])
        Var ann n ->
            sep (PLC.consAnnIf config ann
                [prettyBy config n])
        TyAbs ann tn k t ->
            sexp "abs" (PLC.consAnnIf config ann
                [prettyBy config tn, prettyBy config k, prettyBy config t])
        LamAbs ann n ty t ->
            sexp "lam" (PLC.consAnnIf config ann
                [prettyBy config n, prettyBy config ty, prettyBy config t])
        Apply ann t1 t2 ->
            brackets' (sep (PLC.consAnnIf config ann
                [prettyBy config t1, prettyBy config t2]))
        Constant ann c ->
            sexp "con" (PLC.consAnnIf config ann [prettyTypeOf c, pretty c])
        Builtin ann bi ->
            sexp "builtin" (PLC.consAnnIf config ann
                [pretty bi])
        TyInst ann t ty ->
            braces' (sep (PLC.consAnnIf config ann
                [prettyBy config t, prettyBy config ty]))
        Error ann ty ->
            sexp "error" (PLC.consAnnIf config ann
                [prettyBy config ty])
        IWrap ann ty1 ty2 t ->
            sexp "iwrap" (PLC.consAnnIf config ann
                [prettyBy config ty1, prettyBy config ty2, prettyBy config t])
        Unwrap ann t ->
            sexp "unwrap" (PLC.consAnnIf config ann
                [prettyBy config t])
      where
        prettyTypeOf :: PLC.GShow t => PLC.Some (PLC.ValueOf t) -> Doc dann
        prettyTypeOf (PLC.Some (PLC.ValueOf uni _ )) = pretty $ PLC.SomeTypeIn uni


instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Program tyname name uni fun ann) where
    prettyBy config (Program ann t) =
        sexp "program" (PLC.consAnnIf config ann [prettyBy config t])

-- See note [Default pretty instances for PLC]
instance (PLC.PrettyClassic tyname, Pretty ann) =>
    Pretty (TyVarDecl tyname ann) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic tyname
         , PLC.PrettyClassic name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => Pretty (VarDecl tyname name uni fun ann) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic tyname
         , PLC.PrettyClassic name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => Pretty (Datatype tyname name uni fun ann) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic tyname
         , PLC.PrettyClassic name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => Pretty (Binding tyname name uni fun ann) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic tyname
         , PLC.PrettyClassic name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => Pretty (Term tyname name uni fun ann) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic tyname
         , PLC.PrettyClassic name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => Pretty (Program tyname name uni fun ann) where
    pretty = PLC.prettyClassicDef
