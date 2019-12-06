-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Core.Instance.Pretty.Readable () where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Pretty.Utils

import           Data.Text.Prettyprint.Doc.Internal              (enclose)

-- | Pretty-print a binding at the type level.
prettyTypeBinding
    :: PrettyReadableBy configName (tyname a)
    => PrettyConfigReadable configName -> tyname a -> Kind a -> Doc ann
prettyTypeBinding config name kind
    | _pcrShowKinds config == ShowKindsYes = parens $ prName <+> "::" <+> prettyInBotBy config kind
    | otherwise                            = prName
    where prName = prettyBy config name

instance PrettyBy (PrettyConfigReadable configName) (Kind a) where
    prettyBy config = \case
        Type{}          -> unitaryDoc config "*"
        KindArrow _ k l -> arrowDoc   config k l

instance PrettyBy (PrettyConfigReadable configName) (Constant a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinInt _ int -> pretty int
        BuiltinBS _ bs   -> prettyBytes bs
        BuiltinStr _ str -> pretty str

instance PrettyBy (PrettyConfigReadable configName) (Builtin a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinName    _ name -> pretty name
        DynBuiltinName _ name -> pretty name

instance PrettyReadableBy configName (tyname a) =>
        PrettyBy (PrettyConfigReadable configName) (Type tyname a) where
    prettyBy config = \case
        TyApp _ fun arg         -> applicationDoc config fun arg
        TyVar _ name            -> unit $ prettyName name
        TyFun _ tyIn tyOut      -> arrowDoc config tyIn tyOut
        TyIFix _ pat arg        -> rayR juxtApp $ \juxt -> "ifix" <+> juxt pat <+> juxt arg
        TyForall _ name kind ty -> bind $ \bindBody ->
            "all" <+> prettyTypeBinding config name kind <> "." <+> bindBody ty
        TyBuiltin _ builtin     -> unit $ pretty builtin
        TyLam _ name kind ty    -> bind $ \bindBody ->
            "\\" <> prettyTypeBinding config name kind <+> "->" <+> bindBody ty
      where
        prettyName = prettyBy config
        unit = unitaryDoc config
        rayR = rayDoc config Forward
        bind = binderDoc  config

instance (PrettyReadableBy configName (tyname a), PrettyReadableBy configName (name a)) =>
        PrettyBy (PrettyConfigReadable configName) (Term tyname name a) where
    prettyBy config = \case
        Constant _ con         -> prettyBy config con
        Builtin _ bi           -> prettyBy config bi
        Apply _ fun arg        -> applicationDoc config fun arg
        Var _ name             -> unit $ prettyName name
        TyAbs _ name kind body -> bind $ \bindBody ->
            "/\\" <> prettyTypeBinding config name kind <+> "->" <+> bindBody body
        TyInst _ fun ty        -> rayL juxtApp $ \juxt -> juxt fun <+> inBraces ty
        LamAbs _ name ty body  -> bind $ \bindBody ->
            "\\" <> parens (prettyName name <+> ":" <+> inBot ty) <+> "->" <+> bindBody body
        Unwrap _ term          -> rayR juxtApp $ \juxt -> "unwrap" <+> juxt term
        IWrap _ pat arg term   -> rayR juxtApp $ \juxt ->
            "iwrap" <+> juxt pat <+> juxt arg <+> juxt term
        Error _ ty             -> comp juxtApp $ \_ _ -> "error" <+> inBraces ty
      where
        prettyName = prettyBy config
        unit = unitaryDoc  config
        bind = binderDoc   config
        rayL = rayDoc      config Backward
        rayR = rayDoc      config Forward
        comp = compoundDoc config
        inBot    = prettyInBotBy config
        inBraces = enclose "{" "}" . inBot

instance PrettyReadableBy configName (Term tyname name a) =>
        PrettyBy (PrettyConfigReadable configName) (Program tyname name a) where
    prettyBy config (Program _ version term) =
        rayDoc config Forward juxtApp $ \juxt -> "program" <+> pretty version <+> juxt term
