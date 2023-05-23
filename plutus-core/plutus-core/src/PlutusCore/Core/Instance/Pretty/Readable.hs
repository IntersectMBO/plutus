-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module PlutusCore.Core.Instance.Pretty.Readable () where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable

import Data.Void
import Prettyprinter
import Prettyprinter.Custom
import Universe

-- | Split an iterated 'TyForall' (if any) into a list of variables that it binds and its body.
viewTyForall :: Type tyname uni ann -> Maybe ([TyVarDecl tyname ann], Type tyname uni ann)
viewTyForall ty0@TyForall{} = Just $ go ty0 where
    go (TyForall ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go ty                            = ([], ty)
viewTyForall _ = Nothing

-- | Split an iterated 'TyLam' (if any) into a list of variables that it binds and its body.
viewTyLam :: Type tyname uni ann -> Maybe ([TyVarDecl tyname ann], Type tyname uni ann)
viewTyLam ty0@TyLam{} = Just $ go ty0 where
    go (TyLam ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go ty                         = ([], ty)
viewTyLam _ = Nothing

-- | Split an iterated 'LamAbs' (if any) into a list of variables that it binds and its body.
viewLamAbs
    :: Term tyname name uni fun ann
    -> Maybe ([VarDecl tyname name uni ann], Term tyname name uni fun ann)
viewLamAbs term0@LamAbs{} = Just $ go term0 where
    go (LamAbs ann name ty body) = first (VarDecl ann name ty :) $ go body
    go term                      = ([], term)
viewLamAbs _ = Nothing

-- | Split an iterated 'TyAbs' (if any) into a list of variables that it binds and its body.
viewTyAbs
    :: Term tyname name uni fun ann -> Maybe ([TyVarDecl tyname ann], Term tyname name uni fun ann)
viewTyAbs term0@TyAbs{} = Just $ go term0 where
    go (TyAbs ann name kind body) = first (TyVarDecl ann name kind :) $ go body
    go term                       = ([], term)
viewTyAbs _ = Nothing

-- | Split an iterated 'TyApp' (if any) into the head of the application and the spine.
viewTyApp
    :: Type tyname uni ann -> Maybe (Type tyname uni ann, [Either Void (Type tyname uni ann)])
viewTyApp ty0 = go ty0 [] where
    go (TyApp _ fun arg) args = go fun $ Right arg : args
    go _                 []   = Nothing
    go fun               args = Just (fun, args)

-- | Split an iterated 'Apply'/'TyInst' (if any) into the head of the application and the spine.
viewApp
    :: Term tyname name uni fun ann
    -> Maybe
        ( Term tyname name uni fun ann
        , [Either (Type tyname uni ann) (Term tyname name uni fun ann)]
        )
viewApp term0 = go term0 [] where
    go (Apply _ fun argTerm) args = go fun $ Right argTerm : args
    go (TyInst _ fun argTy)  args = go fun $ Left argTy : args
    go _                     []   = Nothing
    go fun                   args = Just (fun, args)

instance PrettyReadableBy configName tyname =>
        PrettyBy (PrettyConfigReadable configName) (TyVarDecl tyname ann) where
  prettyBy = inContextM $ \case
      TyVarDecl _ x k -> do
          showKinds <- view $ prettyConfig . pcrShowKinds
          withPrettyAt ToTheRight botFixity $ \prettyBot -> do
              case showKinds of
                  ShowKindsYes -> encloseM binderFixity $ prettyBot x <?> "::" <+> prettyBot k
                  ShowKindsNonType -> case k of
                      Type{} -> pure $ prettyBot x
                      _      -> encloseM binderFixity $ prettyBot x <?> "::" <+> prettyBot k
                  ShowKindsNo -> pure $ prettyBot x

instance
        ( PrettyReadableBy configName tyname
        , PrettyReadableBy configName name
        , PrettyUni uni
        ) => PrettyBy (PrettyConfigReadable configName) (VarDecl tyname name uni ann) where
  prettyBy = inContextM $ \case
      VarDecl _ x t -> do
          withPrettyAt ToTheRight botFixity $ \prettyBot -> do
              encloseM binderFixity $ prettyBot x <?> ":" <+> prettyBot t

instance PrettyBy (PrettyConfigReadable configName) (Kind a) where
    prettyBy = inContextM $ \case
        Type{}          -> "*"
        KindArrow _ k l -> k `arrowPrettyM` l

instance (PrettyReadableBy configName tyname, PrettyParens (SomeTypeIn uni)) =>
            PrettyBy (PrettyConfigReadable configName) (Type tyname uni a) where
    prettyBy = inContextM $ \case
        (viewTyApp -> Just (fun, args)) -> iterAppPrettyM fun args
        TyApp {} -> error "Panic: 'TyApp' is not covered by 'viewTyApp'"
        TyVar _ name -> prettyM name
        TyFun _ tyIn tyOut -> tyIn `arrowPrettyM` tyOut
        TyIFix _ pat arg ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "ifix" <+> prettyEl pat <+> prettyEl arg
        (viewTyForall -> Just (args, body)) -> iterTyForallPrettyM args body
        TyForall {} -> error "Panic: 'TyForall' is not covered by 'viewTyForall'"
        TyBuiltin _ builtin -> lmap _pcrRenderContext $ prettyM builtin
        (viewTyLam -> Just (args, body)) -> iterLamAbsPrettyM args body
        TyLam {} -> error "Panic: 'TyLam' is not covered by 'viewTyLam'"
        TySOP _ tls ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                hsep ("sop":fmap prettyEl tls)

instance
        ( PrettyReadableBy configName tyname
        , PrettyReadableBy configName name
        , PrettyUni uni
        , Pretty fun
        ) => PrettyBy (PrettyConfigReadable configName) (Term tyname name uni fun a) where
    prettyBy = inContextM $ \case
        Constant _ con -> unitDocM $ pretty con
        Builtin _ bi -> unitDocM $ pretty bi
        (viewApp -> Just (fun, args)) -> iterAppPrettyM fun args
        Apply {} -> error "Panic: 'Apply' is not covered by 'viewApp'"
        TyInst {} -> error "Panic: 'TyInst' is not covered by 'viewApp'"
        Var _ name -> prettyM name
        (viewTyAbs -> Just (args, body)) -> iterTyAbsPrettyM args body
        TyAbs {} -> error "Panic: 'TyAbs' is not covered by 'viewTyAbs'"
        (viewLamAbs -> Just (args, body)) -> iterLamAbsPrettyM args body
        LamAbs {} -> error "Panic: 'LamAbs' is not covered by 'viewLamAbs'"
        Unwrap _ term ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "unwrap" <+> prettyEl term
        IWrap _ pat arg term ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "iwrap" <+> prettyEl pat <+> prettyEl arg <+> prettyEl term
        Error _ ty ->
            compoundDocM juxtFixity $ \prettyIn ->
                "error" <+> braces (prettyIn ToTheRight botFixity ty)
        Constr _ ty i es -> sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
          "constr" <+> prettyEl ty <+> prettyEl i <+> prettyEl es
        Case _ ty arg cs -> sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
          "case" <+> prettyEl ty <+> prettyEl arg <+> prettyEl cs

instance PrettyReadableBy configName (Term tyname name uni fun a) =>
        PrettyBy (PrettyConfigReadable configName) (Program tyname name uni fun a) where
    prettyBy = inContextM $ \(Program _ version term) ->
        sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
            "program" <+> pretty version <+> prettyEl term
