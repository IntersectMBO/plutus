{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A "readable" Agda-like way to pretty-print PLC entities.
module PlutusCore.Core.Instance.Pretty.Readable () where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable

import Prettyprinter
import Prettyprinter.Custom
import Universe

-- | Split an iterated 'KindArrow' (if any) into the list of argument types and the resulting type.
viewKindArrow :: Kind ann -> Maybe ([Kind ann], Kind ann)
viewKindArrow kind0@KindArrow {} = Just $ go kind0
  where
    go (KindArrow _ dom cod) = first (dom :) $ go cod
    go kind = ([], kind)
viewKindArrow _ = Nothing

-- | Split an iterated 'TyFun' (if any) into the list of argument types and the resulting type.
viewTyFun :: Type tyname uni ann -> Maybe ([Type tyname uni ann], Type tyname uni ann)
viewTyFun ty0@TyFun {} = Just $ go ty0
  where
    go (TyFun _ dom cod) = first (dom :) $ go cod
    go ty = ([], ty)
viewTyFun _ = Nothing

-- | Split an iterated 'TyForall' (if any) into a list of variables that it binds and its body.
viewTyForall :: Type tyname uni ann -> Maybe ([TyVarDecl tyname ann], Type tyname uni ann)
viewTyForall ty0@TyForall {} = Just $ go ty0
  where
    go (TyForall ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go ty = ([], ty)
viewTyForall _ = Nothing

-- | Split an iterated 'TyLam' (if any) into a list of variables that it binds and its body.
viewTyLam :: Type tyname uni ann -> Maybe ([TyVarDecl tyname ann], Type tyname uni ann)
viewTyLam ty0@TyLam {} = Just $ go ty0
  where
    go (TyLam ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go ty = ([], ty)
viewTyLam _ = Nothing

-- | Split an iterated 'LamAbs' (if any) into a list of variables that it binds and its body.
viewLamAbs
  :: Term tyname name uni fun ann
  -> Maybe ([VarDecl tyname name uni ann], Term tyname name uni fun ann)
viewLamAbs term0@LamAbs {} = Just $ go term0
  where
    go (LamAbs ann name ty body) = first (VarDecl ann name ty :) $ go body
    go term = ([], term)
viewLamAbs _ = Nothing

-- | Split an iterated 'TyAbs' (if any) into a list of variables that it binds and its body.
viewTyAbs
  :: Term tyname name uni fun ann -> Maybe ([TyVarDecl tyname ann], Term tyname name uni fun ann)
viewTyAbs term0@TyAbs {} = Just $ go term0
  where
    go (TyAbs ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go term = ([], term)
viewTyAbs _ = Nothing

-- | Split an iterated 'TyApp' (if any) into the head of the application and the spine.
viewTyApp
  :: Type tyname uni ann -> Maybe (Type tyname uni ann, [Type tyname uni ann])
viewTyApp ty0 = go ty0 []
  where
    go (TyApp _ fun arg) args = go fun $ arg : args
    go _ [] = Nothing
    go fun args = Just (fun, args)

-- | Split an iterated 'Apply'/'TyInst' (if any) into the head of the application and the spine.
viewApp
  :: Term tyname name uni fun ann
  -> Maybe
       ( Term tyname name uni fun ann
       , [Either (Type tyname uni ann) (Term tyname name uni fun ann)]
       )
viewApp term0 = go term0 []
  where
    go (Apply _ fun argTerm) args = go fun $ Right argTerm : args
    go (TyInst _ fun argTy) args = go fun $ Left argTy : args
    go _ [] = Nothing
    go fun args = Just (fun, args)

instance
  PrettyReadableBy configName tyname
  => PrettyBy (PrettyConfigReadable configName) (TyVarDecl tyname ann)
  where
  prettyBy = inContextM $ \case
    TyVarDecl _ x k -> do
      showKinds <- view $ prettyConfig . pcrShowKinds
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        case showKinds of
          ShowKindsYes -> encloseM binderFixity $ (prettyBot x <+> "::") <?> prettyBot k
          ShowKindsNonType -> case k of
            Type {} -> pure $ prettyBot x
            _ -> encloseM binderFixity $ (prettyBot x <+> "::") <?> prettyBot k
          ShowKindsNo -> pure $ prettyBot x

instance
  ( PrettyReadableBy configName tyname
  , PrettyReadableBy configName name
  , PrettyUni uni
  )
  => PrettyBy (PrettyConfigReadable configName) (VarDecl tyname name uni ann)
  where
  prettyBy = inContextM $ \case
    VarDecl _ x t -> do
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        encloseM binderFixity $ (prettyBot x <+> ":") <?> prettyBot t

instance PrettyBy (PrettyConfigReadable configName) (Kind a) where
  prettyBy = inContextM $ \case
    (viewKindArrow -> Just (args, res)) -> iterArrowPrettyM args res
    KindArrow {} -> error "Panic: 'KindArrow' is not covered by 'viewKindArrow'"
    Type {} -> "*"

instance
  (PrettyReadableBy configName tyname, PrettyParens (SomeTypeIn uni))
  => PrettyBy (PrettyConfigReadable configName) (Type tyname uni a)
  where
  prettyBy = inContextM $ \case
    (viewTyApp -> Just (fun, args)) -> iterAppPrettyM fun args
    TyApp {} -> error "Panic: 'TyApp' is not covered by 'viewTyApp'"
    TyVar _ name -> prettyM name
    (viewTyFun -> Just (args, res)) -> iterArrowPrettyM args res
    TyFun {} -> error "Panic: 'TyFun' is not covered by 'viewTyFun'"
    TyIFix _ pat arg -> iterAppDocM $ \_ prettyArg -> "ifix" :| map prettyArg [pat, arg]
    (viewTyForall -> Just (args, body)) -> iterTyForallPrettyM args body
    TyForall {} -> error "Panic: 'TyForall' is not covered by 'viewTyForall'"
    TyBuiltin _ someUni -> lmap _pcrRenderContext $ prettyM someUni
    (viewTyLam -> Just (args, body)) -> iterLamAbsPrettyM args body
    TyLam {} -> error "Panic: 'TyLam' is not covered by 'viewTyLam'"
    TySOP _ tls -> iterAppDocM $ \_ prettyArg -> "sop" :| fmap prettyArg tls

instance
  ( PrettyReadableBy configName tyname
  , PrettyReadableBy configName name
  , PrettyUni uni
  , Pretty fun
  )
  => PrettyBy (PrettyConfigReadable configName) (Term tyname name uni fun a)
  where
  prettyBy = inContextM $ \case
    Constant _ con -> lmap (ConstConfig . _pcrRenderContext) $ prettyM con
    Builtin _ bi -> unitDocM $ pretty bi
    (viewApp -> Just (fun, args)) -> iterInterAppPrettyM fun args
    Apply {} -> error "Panic: 'Apply' is not covered by 'viewApp'"
    TyInst {} -> error "Panic: 'TyInst' is not covered by 'viewApp'"
    Var _ name -> prettyM name
    (viewTyAbs -> Just (args, body)) -> iterTyAbsPrettyM args body
    TyAbs {} -> error "Panic: 'TyAbs' is not covered by 'viewTyAbs'"
    (viewLamAbs -> Just (args, body)) -> iterLamAbsPrettyM args body
    LamAbs {} -> error "Panic: 'LamAbs' is not covered by 'viewLamAbs'"
    Unwrap _ term -> iterAppDocM $ \_ prettyArg -> "unwrap" :| [prettyArg term]
    IWrap _ pat arg term ->
      iterAppDocM $ \_ prettyArg ->
        "iwrap" :| [prettyArg pat, prettyArg arg, prettyArg term]
    Error _ ty -> iterAppDocM $ \_ prettyArg -> "error" :| [prettyArg $ inBraces ty]
    Constr _ ty i es ->
      iterAppDocM $ \_ prettyArg -> "constr" :| [prettyArg ty, prettyArg i, prettyArg es]
    Case _ ty arg cs ->
      iterAppDocM $ \_ prettyArg -> "case" :| [prettyArg ty, prettyArg arg, prettyArg cs]

instance
  PrettyReadableBy configName (Term tyname name uni fun a)
  => PrettyBy (PrettyConfigReadable configName) (Program tyname name uni fun a)
  where
  prettyBy = inContextM $ \(Program _ version term) ->
    iterAppDocM $ \_ prettyArg -> "program" :| [pretty version, prettyArg term]
