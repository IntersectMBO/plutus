-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
-- breaks type inference

module PlutusIR.Core.Instance.Pretty.Readable () where

import PlutusCore.Pretty
import PlutusIR.Core.Type
import PlutusPrelude

import Data.Profunctor
import Prettyprinter
import Prettyprinter.Custom

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

-- | Split a 'Let' (if any) into a list of bindings and its body.
viewLet
  :: Term tyname name uni fun ann
  -> Maybe ([(Recursivity, [Binding tyname name uni fun ann])], Term tyname name uni fun ann)
viewLet term0@Let {} = Just $ go term0
  where
    go (Let _ rec binds body) = first ((rec, toList binds) :) $ go body
    go term = ([], term)
viewLet _ = Nothing

type PrettyConstraints configName tyname name uni =
  ( PrettyReadableBy configName tyname
  , PrettyReadableBy configName name
  , PrettyUni uni
  )

instance
  (PrettyConstraints configName tyname name uni, Pretty fun)
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
    (viewLet -> Just (lets, body)) ->
      compoundDocM binderFixity $ \prettyIn ->
        let prettyBot x = prettyIn ToTheRight botFixity x
            prec NonRec = ""
            prec _ = "rec"
            -- nest 2 including the "let": this means that we will always break after the let,
            -- so that the bindings can be simply indented by 2 spaces, keeping the indent low
            prettyLet r binds = vsep [nest 2 ("let" <> prec r <> line <> vcatHard (prettyBot <$> binds)), "in"]
         in -- Lay out let-bindings in a layout-sensitive way
            --
            -- let
            --   !x : t = a
            --   !y : t = b
            -- in
            -- foo x y
            vsep $ [prettyLet r binds | (r, binds) <- lets] ++ [prettyBot body]
    Let {} -> error "Panic: 'Let' is not covered by 'viewLet'"
    Constr _ ty i es ->
      iterAppDocM $ \_ prettyArg -> "constr" :| [prettyArg ty, prettyArg i, prettyArg es]
    Case _ ty arg cs ->
      iterAppDocM $ \_ prettyArg -> "case" :| [prettyArg ty, prettyArg arg, prettyArg cs]

instance
  (PrettyConstraints configName tyname name uni, Pretty fun)
  => PrettyBy (PrettyConfigReadable configName) (Program tyname name uni fun a)
  where
  prettyBy = inContextM $ \(Program _ version term) ->
    iterAppDocM $ \_ prettyArg -> "program" :| [pretty version, prettyArg term]

instance
  (PrettyConstraints configName tyname name uni, Pretty fun)
  => PrettyBy (PrettyConfigReadable configName) (Binding tyname name uni fun ann)
  where
  prettyBy = inContextM $ \case
    TermBind _ s vdec t ->
      -- Layout term bindings in lets like
      --
      --  let !a : t = body
      --
      -- or
      --
      --  let !a : t
      --       = biggerBody
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ (bt <> prettyBot vdec) <?> "=" <+> prettyBot t
      where
        bt
          | Strict <- s = "!"
          | otherwise = "~"
    TypeBind _ tydec a ->
      -- Basically the same as above
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ prettyBot tydec <?> "=" <+> prettyBot a
    DatatypeBind _ dt -> prettyM dt

instance
  PrettyConstraints configName tyname name uni
  => PrettyBy (PrettyConfigReadable configName) (Datatype tyname name uni ann)
  where
  prettyBy = inContextM $ \case
    Datatype _ tydec pars name cs -> do
      -- Layout datatypes as
      --  data (Maybe :: * -> *) a | match_Maybe where
      --    Nothing : D a
      --    Just : a -> D a
      header <- sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
        "data" <+> fillSep (prettyEl tydec : map prettyEl pars) <+> "|" <+> prettyEl name <+> "where"
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ vcatHard [header, indent 2 (align . vcatHard . map prettyBot $ cs)]
