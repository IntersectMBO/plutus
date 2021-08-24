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


import           Data.Text.Prettyprint.Doc.Custom

-- Pretty-printing

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (VarDecl tyname name uni fun ann) where
    prettyBy config (VarDecl ann n ty) =
        parens' ("vardecl" </> vsep' (PLC.consAnnIf config ann [prettyBy config n, prettyBy config ty]))

instance ( PLC.PrettyClassicBy configName tyname
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (TyVarDecl tyname ann) where
    prettyBy config (TyVarDecl ann n ty) =
        parens' ("tyvardecl" </> vsep' (PLC.consAnnIf config ann [prettyBy config n, prettyBy config ty]))

instance PrettyBy (PLC.PrettyConfigClassic configName) Recursivity where
    prettyBy _ = \case
        NonRec -> parens' "nonrec"
        Rec    -> parens' "rec"

instance PrettyBy (PLC.PrettyConfigClassic configName) Strictness where
    prettyBy _ = \case
        NonStrict -> parens' "nonstrict"
        Strict    -> parens' "strict"

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Datatype tyname name uni fun ann) where
    prettyBy config (Datatype ann ty tyvars destr constrs) =
        parens' ("datatype" </> vsep' (PLC.consAnnIf config ann
            [ prettyBy config ty
            , vsep' $ fmap (prettyBy config) tyvars
            , prettyBy config destr
            , vsep' $ fmap (prettyBy config) constrs
            ]))

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Binding tyname name uni fun ann) where
    prettyBy config = \case
        TermBind ann s d t ->
            parens' ("termbind" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config s, prettyBy config d, prettyBy config t]))
        TypeBind ann d ty  ->
            parens' ("typebind" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config d, prettyBy config ty]))
        DatatypeBind ann d ->
            parens' ("datatypebind" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config d]))

instance ( PLC.PrettyClassicBy configName tyname
         , PLC.PrettyClassicBy configName name
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         , Pretty fun
         , Pretty ann
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Term tyname name uni fun ann) where
    prettyBy config = \case
        Let ann r bs t ->
            parens' ("let" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config r, vsep' . toList $ fmap (prettyBy config) bs, prettyBy config t]))
        Var ann n ->
            vsep' (PLC.consAnnIf config ann
                [prettyBy config n])
        TyAbs ann tn k t ->
            parens' ("abs" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config tn, prettyBy config k, prettyBy config t]))
        LamAbs ann n ty t ->
            parens' ("lam" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config n, prettyBy config ty, prettyBy config t]))
        Apply ann t1 t2 ->
            brackets' (vsep' (PLC.consAnnIf config ann
                [prettyBy config t1, prettyBy config t2]))
        Constant ann c ->
            parens' ("con" </> vsep' (PLC.consAnnIf config ann [prettyTypeOf c]) </> pretty c)
        Builtin ann bi ->
            parens' ("builtin" </> vsep' (PLC.consAnnIf config ann
                [pretty bi]))
        TyInst ann t ty ->
            braces' (vsep' (PLC.consAnnIf config ann
                [prettyBy config t, prettyBy config ty]))
        Error ann ty ->
            parens' ("error" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config ty]))
        IWrap ann ty1 ty2 t ->
            parens' ("iwrap" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config ty1, prettyBy config ty2, prettyBy config t]))
        Unwrap ann t ->
            parens' ("unwrap" </> vsep' (PLC.consAnnIf config ann
                [prettyBy config t]))
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
        parens' ("program" </> vsep' (PLC.consAnnIf config ann
            [prettyBy config t]))

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
