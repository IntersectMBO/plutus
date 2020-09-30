-- | A "readable" Agda-like way to pretty-print Untyped Plutus Core terms.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.UntypedPlutusCore.Core.Instance.Pretty.Readable () where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core.Type

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Pretty.PrettyConst
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Universe

import           Data.Text.Prettyprint.Doc

instance
        ( PrettyReadableBy configName name
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst
        ) => PrettyBy (PrettyConfigReadable configName) (Term name uni a) where
    prettyBy = inContextM $ \case
        Constant _ val -> unitDocM $ pretty val
        Builtin _ bi -> unitDocM $ pretty bi
        Var _ name -> prettyM name
        LamAbs _ name body ->
            compoundDocM binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn ToTheRight botFixity x
                in "\\" <> prettyBot name <+> "->" <+> prettyBot body
        Apply _ fun arg -> fun `juxtPrettyM` arg
        Delay _ term ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "delay" <+> prettyEl term
        Force _ term ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "force" <+> prettyEl term
        Error _ -> unitDocM "error"

instance PrettyReadableBy configName (Term name uni a) =>
        PrettyBy (PrettyConfigReadable configName) (Program name uni a) where
    prettyBy = inContextM $ \(Program _ version term) ->
        sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
            "program" <+> pretty version <+> prettyEl term
