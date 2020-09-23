-- | A "classic" (i.e. as seen in the specification) way to pretty-print Untyped Plutus Core terms.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.UntypedPlutusCore.Core.Instance.Pretty.Classic () where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core.Type

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.PrettyConst
import           Language.PlutusCore.Universe

import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Custom

instance (PrettyClassicBy configName name, GShow uni, Closed uni, uni `Everywhere` PrettyConst) =>
            PrettyBy (PrettyConfigClassic configName) (Term name uni a) where
    prettyBy config = go where
        go (Constant _ val)     = parens' $ "con" </> prettyTypeOf val </> pretty val  -- NB: actually calls prettyConst
        go (Builtin _ bi)       = parens' $ "builtin" </> pretty bi
        go (Var _ name)         = prettyName name
        go (LamAbs _ name body) = parens' $ "lam" </> vsep' [prettyName name, go body]
        go (Apply _ fun arg)    = brackets' $ vsep' [go fun, go arg]
        go (Delay _ term)       = parens' ("delay" </> go term)
        go (Force _ term)       = parens' ("force" </> go term)
        go (Error _)            = "error"

        prettyName :: PrettyClassicBy configName n => n -> Doc ann
        prettyName = prettyBy config

        prettyTypeOf :: GShow t => Some (ValueOf t) -> Doc ann
        prettyTypeOf (Some (ValueOf uni _ )) = pretty $ TypeIn uni

instance PrettyClassicBy configName (Term name uni a) =>
        PrettyBy (PrettyConfigClassic configName) (Program name uni a) where
    prettyBy config (Program _ version term) = parens' $ "program" <+> pretty version <//> prettyBy config term
