-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.PlutusCore.Core.Instance.Pretty.Readable () where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Pretty.PrettyM
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Universe

import           Control.Monad.Reader
-- import qualified Data.Text.Prettyprint.Doc.Internal              as Doc (enclose)
import           Data.Text.Prettyprint.Doc.Symbols.Ascii

applicationPM
    :: ( MonadReader env m, HasPrettyConfig env config, HasRenderContext config
       , PrettyM config a, PrettyM config b
       )
    => a -> b -> m (Doc ann)
applicationPM fun arg =
    infixDoc juxtFixity $ \prettyL prettyR -> prettyL fun <+> prettyR arg

-- | Pretty-print a @->@ between two things.
arrowPM
    :: ( MonadReader env m, HasPrettyConfig env config, HasRenderContext config
       , PrettyM config a, PrettyM config b
       )
    => a -> b -> m (Doc ann)
arrowPM a b =
    infixDoc arrowFixity $ \prettyL prettyR -> prettyL a <+> "->" <+> prettyR b

-- | Pretty-print a binding at the type level.
typeBinderDoc
    :: ( MonadReader env m, HasPrettyConfigReadable env configName
       , PrettyReadableBy configName (tyname a)
       )
    => ((tyname a -> Kind a -> Doc ann) -> AnyToDoc (PrettyConfigReadable configName) ann -> Doc ann)
    -> m (Doc ann)
typeBinderDoc k = do
    showKinds <- view $ prettyConfig . pcrShowKinds
    withPrettyAt Forward botFixity $ \prettyBot -> do
        let prettyBind name kind = case showKinds of
                ShowKindsYes -> parens $ prettyBot name <+> "::" <+> prettyBot kind
                ShowKindsNo  -> prettyBot name
        encloseM binderFixity $ k prettyBind prettyBot

instance PrettyM (PrettyConfigReadable configName) (Kind a) where
    prettyM = \case
        Type{}          -> unitaryDoc "*"
        KindArrow _ k l -> k `arrowPM` l

instance (PrettyReadableBy configName (tyname a), GShow uni) =>
        PrettyM (PrettyConfigReadable configName) (Type tyname uni a) where
    prettyM = \case
        TyApp _ fun arg           -> fun `applicationPM` arg
        TyVar _ name              -> prettyM name
        TyFun _ tyIn tyOut        -> tyIn `arrowPM` tyOut
        TyIFix _ pat arg          ->
            sequenceDoc juxtFixity $ \prettyEl -> "ifix" <+> prettyEl pat <+> prettyEl arg
        TyForall _ name kind body ->
            typeBinderDoc $ \prettyBinding prettyBody ->
                "all" <+> prettyBinding name kind <> "." <+> prettyBody body
        TyBuiltin _ builtin       -> unitaryDoc $ pretty builtin
        TyLam _ name kind body    ->
            typeBinderDoc $ \prettyBinding prettyBody ->
                "\\" <> prettyBinding name kind <+> "->" <+> prettyBody body

instance
        ( PrettyReadableBy configName (tyname a)
        , PrettyReadableBy configName (name a)
        , GShow uni, Closed uni, uni `Everywhere` Pretty
        ) => PrettyM (PrettyConfigReadable configName) (Term tyname name uni a) where
    prettyM = \case
        Constant _ con         -> unitaryDoc $ pretty con
        Builtin _ bi           -> unitaryDoc $ pretty bi
        Apply _ fun arg        -> fun `applicationPM` arg
        Var _ name             -> prettyM name
        TyAbs _ name kind body ->
            typeBinderDoc $ \prettyBinding prettyBody ->
                "/\\" <> prettyBinding name kind <+> "->" <+> prettyBody body
        TyInst _ fun ty        ->
            compoundDoc juxtFixity $ \prettyIn ->
                prettyIn Backward juxtFixity fun <+> braces (prettyIn Forward botFixity ty)
        LamAbs _ name ty body  ->
            compoundDoc binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn Forward botFixity x
                in "\\" <> parens (prettyBot name <+> ":" <+> prettyBot ty) <+> "->" <+> prettyBot body
        Unwrap _ term          ->
            sequenceDoc juxtFixity $ \prettyEl -> "unwrap" <+> prettyEl term
        IWrap _ pat arg term   ->
            sequenceDoc juxtFixity $ \prettyEl ->
                "iwrap" <+> prettyEl pat <+> prettyEl arg <+> prettyEl term
        Error _ ty             ->
            compoundDoc juxtFixity $ \prettyIn ->
                "error" <+> braces (prettyIn Forward botFixity ty)

instance PrettyReadableBy configName (Term tyname name uni a) =>
        PrettyM (PrettyConfigReadable configName) (Program tyname name uni a) where
    prettyM (Program _ version term) =
        sequenceDoc juxtFixity $ \prettyEl -> "program" <+> pretty version <+> prettyEl term
