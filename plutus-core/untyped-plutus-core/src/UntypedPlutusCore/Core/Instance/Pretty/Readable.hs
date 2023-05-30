{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A "readable" Agda-like way to pretty-print Untyped Plutus Core terms.
module UntypedPlutusCore.Core.Instance.Pretty.Readable () where

import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable
import PlutusPrelude
import UntypedPlutusCore.Core.Type

import Data.Void
import Prettyprinter

-- | Split an iterated 'LamAbs' (if any) into a list of variables that it binds and its body.
viewLamAbs :: Term name uni fun ann -> Maybe ([name], Term name uni fun ann)
viewLamAbs term0@LamAbs{} = Just $ go term0
  where
    go (LamAbs _ name body) = first (name :) $ go body
    go term                 = ([], term)
viewLamAbs _ = Nothing

-- | Split an iterated 'Apply' (if any) into the head of the application and the spine.
viewApp ::
  Term name uni fun ann ->
  Maybe (Term name uni fun ann, [Either Void (Term name uni fun ann)])
viewApp term0 = go term0 []
  where
    go (Apply _ fun argTerm) args = go fun $ Right argTerm : args
    go _ []                       = Nothing
    go fun args                   = Just (fun, args)

instance
  (PrettyReadableBy configName name, PrettyUni uni, Pretty fun) =>
  PrettyBy (PrettyConfigReadable configName) (Term name uni fun a)
  where
  prettyBy = inContextM $ \case
    Constant _ val -> unitDocM $ pretty val
    Builtin _ bi -> unitDocM $ pretty bi
    Var _ name -> prettyM name
    (viewLamAbs -> Just (args, body)) -> iterLamAbsPrettyM args body
    LamAbs{} -> error "Panic: 'LamAbs' is not covered by 'viewLamAbs'"
    (viewApp -> Just (fun, args)) -> iterAppPrettyM fun args
    Apply{} -> error "Panic: 'Apply' is not covered by 'viewApp'"
    Delay _ term ->
      sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
        "delay" <+> prettyEl term
    Force _ term ->
      sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
        "force" <+> prettyEl term
    Error _ -> unitDocM "error"
    Constr _ i es -> sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
      "constr" <+> prettyEl i <+> prettyEl es
    Case _ arg cs -> sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
      "case" <+> prettyEl arg <+> prettyEl cs

instance
  (PrettyReadableBy configName (Term name uni fun a)) =>
  PrettyBy (PrettyConfigReadable configName) (Program name uni fun a)
  where
  prettyBy = inContextM $ \(Program _ version term) ->
    sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
      "program" <+> pretty version <+> prettyEl term
