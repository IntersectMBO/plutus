{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A "readable" Agda-like way to pretty-print Untyped Plutus Core terms.
module UntypedPlutusCore.Core.Instance.Pretty.Readable () where

import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable
import PlutusPrelude
import UntypedPlutusCore.Core.Type

import Prettyprinter

-- | Split an iterated 'LamAbs' (if any) into a list of variables that it binds and its body.
viewLamAbs :: Term name uni fun ann -> Maybe ([name], Term name uni fun ann)
viewLamAbs term0@LamAbs {} = Just $ go term0
  where
    go (LamAbs _ name body) = first (name :) $ go body
    go term = ([], term)
viewLamAbs _ = Nothing

-- | Split an iterated 'Apply' (if any) into the head of the application and the spine.
viewApp
  :: Term name uni fun ann
  -> Maybe (Term name uni fun ann, [Term name uni fun ann])
viewApp term0 = go term0 []
  where
    go (Apply _ fun arg) args = go fun $ arg : args
    go _ [] = Nothing
    go fun args = Just (fun, args)

instance
  (PrettyReadableBy configName name, PrettyUni uni, Pretty fun, Show configName)
  => PrettyBy (PrettyConfigReadable configName) (Term name uni fun a)
  where
  prettyBy = inContextM $ \case
    Constant _ val -> lmap (ConstConfig . _pcrRenderContext) $ prettyM val
    Builtin _ bi -> unitDocM $ pretty bi
    Var _ name -> prettyM name
    (viewLamAbs -> Just (args, body)) -> iterLamAbsPrettyM args body
    LamAbs {} -> error "Panic: 'LamAbs' is not covered by 'viewLamAbs'"
    (viewApp -> Just (fun, args)) -> iterAppPrettyM fun args
    Apply {} -> error "Panic: 'Apply' is not covered by 'viewApp'"
    Delay _ term -> iterAppDocM $ \_ prettyArg -> "delay" :| [prettyArg term]
    Force _ term -> iterAppDocM $ \_ prettyArg -> "force" :| [prettyArg term]
    Error _ -> unitDocM "error"
    -- Always rendering the tag on the same line for more compact output, it's just a tiny integer
    -- anyway.
    Constr _ i es -> iterAppDocM $ \_ prettyArg ->
      ("constr" <+> prettyArg i) :| [prettyArg es]
    Case _ arg cs -> iterAppDocM $ \_ prettyArg -> "case" :| [prettyArg arg, prettyArg (toList cs)]

instance
  PrettyReadableBy configName (Term name uni fun a)
  => PrettyBy (PrettyConfigReadable configName) (Program name uni fun a)
  where
  prettyBy = inContextM $ \(Program _ version term) ->
    iterAppDocM $ \_ prettyArg -> "program" :| [pretty version, prettyArg term]
