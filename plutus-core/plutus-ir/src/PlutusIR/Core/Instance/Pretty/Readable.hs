-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module PlutusIR.Core.Instance.Pretty.Readable
  ( prettyPirReadable
  , PrettyPir
  ) where

import PlutusCore.Default.Universe
import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable
import PlutusIR.Core.Type
import PlutusPrelude
import Prettyprinter
import Prettyprinter.Custom

type PrettyPir = PrettyBy (PrettyConfigReadable PrettyConfigName)

-- | Pretty-print something with the Pir prettyprinter settings.
prettyPirReadable :: PrettyPir a => a -> Doc ann
prettyPirReadable = prettyBy prettyConfigReadable
  -- Using 'debugPrettyConfigName', because it's actually helpful unlike 'defPrettyConfigName'.
  where prettyConfigReadable = botPrettyConfigReadable debugPrettyConfigName def

-- | Split an application into its (possible) head and arguments (either types or term)
viewApp :: Term tyname name uni fun ann
        -> Maybe (Term tyname name uni fun ann, [Either (Type tyname uni ann) (Term tyname name uni fun ann)])
viewApp t = go t []
  where
    go (Apply _ t s)  args = go t (Right s : args)
    go (TyInst _ t a) args = go t (Left a : args)
    go t args              = if null args then Nothing else Just (t, args)

-- | Split a type abstraction into it's possible components.
viewTyAbs :: Term tyname name uni fun ann -> Maybe ([TyVarDecl tyname ()], Term tyname name uni fun ann)
viewTyAbs t@TyAbs{} = Just (go t)
  where go (TyAbs _ n k b) = first ((TyVarDecl () n (void k)):) $ go b
        go t               = ([], t)
viewTyAbs _         = Nothing

-- | Split a term abstraction into it's possible components.
viewLam :: Term tyname name uni fun ann -> Maybe ([VarDecl tyname name uni ()], Term tyname name uni fun ann)
viewLam t@LamAbs{} = Just (go t)
  where go (LamAbs _ n t b) = first ((VarDecl () n (void t)):) $ go b
        go t                = ([], t)
viewLam _          = Nothing

-- | Split a let into a sequence of lets and its remaining body
viewLet :: Term tyname name uni fun ann -> Maybe ([(Recursivity, [Binding tyname name uni fun ann])], Term tyname name uni fun ann)
viewLet t@Let{} = Just (go t)
  where go (Let _ r bs b) = first ((r, toList bs):) $ go b
        go t              = ([], t)
viewLet _       = Nothing

type PrettyConstraints configName tyname name uni =
  ( PrettyReadableBy configName tyname
  , PrettyReadableBy configName name
  , Pretty (SomeTypeIn uni)
  , Closed uni, uni `Everywhere` PrettyConst
  )

instance (PrettyConstraints configName tyname name uni, Pretty fun)
          => PrettyBy (PrettyConfigReadable configName) (Term tyname name uni fun a) where
    prettyBy = inContextM $ \case
        Constant _ con -> unitDocM $ pretty con
        Builtin _ bi   -> unitDocM $ pretty bi
        (viewApp -> Just (fun, args)) ->
          compoundDocM juxtFixity $ \ prettyIn ->
            let ppArg (Left a)  = braces $ prettyIn ToTheRight botFixity a
                ppArg (Right t) = prettyIn ToTheRight juxtFixity t
            -- Using `align` here and gathering the arguments together helps to lay out
            -- function applications compactly like:
            --
            -- foo a b c
            --     d e f
            --
            -- or
            --
            -- foo
            --  veryLongArg
            --  a b c
            --
            in prettyIn ToTheLeft juxtFixity fun <?> align (fillSep (map ppArg args))
        Apply{}    -> error "The impossible happened. This should be covered by the `viewApp` case above."
        TyInst{}   -> error "The impossible happened. This should be covered by the `viewApp` case above."
        Var _ name -> prettyM name
        (viewTyAbs -> Just (args, body)) ->
            withPrettyAt ToTheRight botFixity $ \ prettyBot -> do
                let pBody = prettyBot body
                pBinds <- mapM prettyM args
                -- See comment below about laying out lambdas
                encloseM binderFixity $ ("/\\" <> align (fillSep pBinds) <+> "->") <?> pBody
        TyAbs{}    -> error "The impossible happened. This should be covered by the `viewTyAbs` case above."
        (viewLam -> Just (args, body)) ->
            -- Lay out abstraction like
            --  \ (x : t) (y : t')
            --    (z : t'') -> body
            -- or
            --  \ (x : t) (y : t')
            --    (z : t'') ->
            --    bigStartOfBody
            compoundDocM binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn ToTheRight botFixity x
                    prettyBinds = align . fillSep . map (prettyIn ToTheLeft binderFixity) $ args
                in ("\\" <> prettyBinds <+> "->") <?> prettyBot body
        LamAbs{}   -> error "The impossible happened. This should be covered by the `viewLam` case above."
        Unwrap _ term          ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "unwrap" <+> prettyEl term
        IWrap _ pat arg term   ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "iwrap" <+> prettyEl pat <+> prettyEl arg <+> prettyEl term
        Error _ ty             ->
            compoundDocM juxtFixity $ \prettyIn ->
                "error" <+> braces (prettyIn ToTheRight botFixity ty)
        (viewLet -> Just (lets, body)) ->
            compoundDocM binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn ToTheRight botFixity x
                    prec NonRec = ""
                    prec _      = "rec"
                -- Lay out let-bindings in a layout-sensitive way
                --
                -- let !x : t = a
                -- in
                -- let !y : t = b
                -- in foo x y
                in align (sep [ sep ["let" <> prec r <+> align (vcatHard (prettyBot <$> binds)), "in"]
                              | (r, binds) <- lets ]) <+> prettyBot body
        Let{} -> error "The impossible happened. This should be covered by the `viewLet` case above."
        Constr{} -> unitDocM "constr"
        Case{} -> unitDocM "case"

instance (PrettyConstraints configName tyname name uni, Pretty fun)
          => PrettyBy (PrettyConfigReadable configName) (Binding tyname name uni fun ann) where
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
        bt | Strict <- s = "!"
           | otherwise   = "~"
    TypeBind _ tydec a ->
      -- Basically the same as above
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ prettyBot tydec <?> "=" <+> prettyBot a
    DatatypeBind _ dt -> prettyM dt

instance PrettyConstraints configName tyname name uni
          => PrettyBy (PrettyConfigReadable configName) (Datatype tyname name uni ann) where
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

instance PrettyReadableBy configName tyname
          => PrettyBy (PrettyConfigReadable configName) (TyVarDecl tyname ann) where
  prettyBy = inContextM $ \case
    TyVarDecl _ x k -> do
      showKinds <- view $ prettyConfig . pcrShowKinds
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        case showKinds of
          ShowKindsYes -> encloseM binderFixity (sep [prettyBot x, "::" <+> prettyBot k])
          ShowKindsNonType -> case k of
            Type{} -> return $ prettyBot x
            _      -> encloseM binderFixity (sep [prettyBot x, "::" <+> prettyBot k])
          ShowKindsNo -> return $ prettyBot x

instance PrettyConstraints configName tyname name uni
          => PrettyBy (PrettyConfigReadable configName) (VarDecl tyname name uni ann) where
  prettyBy = inContextM $ \case
    VarDecl _ x t -> do
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        encloseM binderFixity (sep [prettyBot x, ":" <+> prettyBot t])
