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
module PlutusIR.Core.Instance.Pretty.Readable where

import PlutusCore.Core.Instance.Pretty.Readable
import PlutusCore.Default.Universe
import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.PrettyConst
import PlutusCore.Pretty.Readable
import PlutusIR.Core.Type
import PlutusPrelude
import Prettyprinter

prettyConfigReadable :: PrettyConfigReadable PrettyConfigName
prettyConfigReadable = botPrettyConfigReadable defPrettyConfigName ShowKindsYes

prettyReadable :: PrettyBy (PrettyConfigReadable PrettyConfigName) a => a -> Doc ann
prettyReadable = prettyBy prettyConfigReadable

viewApp :: Term tyname name uni fun ann
        -> Maybe (Term tyname name uni fun ann, [Either (Type tyname uni ann) (Term tyname name uni fun ann)])
viewApp t = go t []
  where
    go (Apply _ t s)  args = go t (Right s : args)
    go (TyInst _ t a) args = go t (Left a : args)
    go t args              = if null args then Nothing else Just (t, args)

vcatHard :: [Doc ann] -> Doc ann
vcatHard = concatWith (\x y -> x <> hardline <> y)

(<?>) :: Doc ann -> Doc ann -> Doc ann
p <?> q = align . nest 2 $ sep [p, q]

infixr 6 <?>

type PrettyConstraints configName tyname name uni fun =
  ( PrettyReadableBy configName tyname
  , PrettyReadableBy configName name
  , GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun
  )

instance PrettyConstraints configName tyname name uni fun
          => PrettyBy (PrettyConfigReadable configName) (Term tyname name uni fun a) where
    prettyBy = inContextM $ \case
        Constant _ con -> unitDocM $ pretty con
        Builtin _ bi   -> unitDocM $ pretty bi
        (viewApp -> Just (fun, args)) ->
          compoundDocM juxtFixity $ \ prettyIn ->
            let ppArg (Left a)  = braces $ prettyIn ToTheRight botFixity a
                ppArg (Right t) = prettyIn ToTheRight juxtFixity t
            in prettyIn ToTheLeft juxtFixity fun <?> fillSep (map ppArg args)
        Apply{}    -> error "The impossible happened. This should be covered by the `viewApp` case above."
        TyInst{}   -> error "The impossible happened. This should be covered by the `viewApp` case above."
        Var _ name -> prettyM name
        t@TyAbs{}  ->
            typeBinderDocM $ \prettyBinding prettyBody ->
                ("/\\" <> align (fillSep (map (uncurry prettyBinding) args)) <+> "->") <?> prettyBody body
            where (args, body)         = view t
                  view (TyAbs _ n k b) = first ((n, k):) $ view b
                  view t               = ([], t)
        t@LamAbs{}  ->
            compoundDocM binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn ToTheRight botFixity x
                in ("\\" <> align (fillSep [ parens (prettyBot name <+> ":" <+> prettyBot ty)
                                           | (name, ty) <- args ]) <+> "->") <?> prettyBot body
            where (args, body)          = view t
                  view (LamAbs _ n t b) = first ((n, t):) $ view b
                  view t                = ([], t)
        Unwrap _ term          ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "unwrap" <+> prettyEl term
        IWrap _ pat arg term   ->
            sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
                "iwrap" <+> prettyEl pat <+> prettyEl arg <+> prettyEl term
        Error _ ty             ->
            compoundDocM juxtFixity $ \prettyIn ->
                "error" <+> braces (prettyIn ToTheRight botFixity ty)
        Let _ rec binds t         ->
            compoundDocM binderFixity $ \prettyIn ->
                let prettyBot x = prettyIn ToTheRight botFixity x
                    prec | rec == NonRec = ""
                         | otherwise     = "rec"
                in align $ sep [ "let" <> prec <+> align (vcatHard (prettyBot <$> toList binds))
                               , "in"
                               , prettyBot t
                               ]

instance PrettyConstraints configName tyname name uni fun
          => PrettyBy (PrettyConfigReadable configName) (Binding tyname name uni fun ann) where
  prettyBy = inContextM $ \case
    TermBind _ s vdec t ->
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ (bt <> prettyBot vdec) <?> "=" <+> prettyBot t
      where
        bt | Strict <- s = "!"
           | otherwise   = "~"
    TypeBind _ tydec a ->
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        return $ prettyBot tydec <+> "=" <?> prettyBot a
    DatatypeBind _ dt -> prettyM dt

instance PrettyConstraints configName tyname name uni fun
          => PrettyBy (PrettyConfigReadable configName) (Datatype tyname name uni fun ann) where
  prettyBy = inContextM $ \case
    Datatype _ tydec pars name cs -> do
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
        case k of
          Type _ -> return $ prettyBot x
          _ | ShowKindsYes <- showKinds ->
                  encloseM binderFixity (sep [prettyBot x, "::" <+> prettyBot k])
               | otherwise -> return $ prettyBot x

instance PrettyConstraints configName tyname name uni fun
          => PrettyBy (PrettyConfigReadable configName) (VarDecl tyname name uni fun ann) where
  prettyBy = inContextM $ \case
    VarDecl _ x t -> do
      withPrettyAt ToTheRight botFixity $ \prettyBot -> do
        encloseM binderFixity (sep [prettyBot x, ":" <+> prettyBot t])
