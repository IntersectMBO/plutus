{-# LANGUAGE OverloadedStrings #-}

{-| Custom width-aware pretty-printer for Template Haskell declarations.

Replaces @TH.pprint@ + @formatTHOutput@ for golden test output, using the
@prettyprinter@ library's Wadler\/Lindig algorithm to produce readable output
that respects a configurable page width (default 100 columns). -}
module PlutusTx.Test.THPretty (pprintDecs) where

import Prelude

import Data.Char (isAlphaNum)
import Language.Haskell.TH qualified as TH
import Prettyprinter
import Prettyprinter.Render.String (renderString)

-- | Pretty-print a list of TH declarations with width-aware layout.
pprintDecs :: [TH.Dec] -> String
pprintDecs decs = renderString $ layoutSmart opts $ vsep (map ppDec decs)
  where
    opts = LayoutOptions (AvailablePerLine 100 1.0)

------------------------------------------------------------
-- Declarations
------------------------------------------------------------

ppDec :: TH.Dec -> Doc ann
ppDec (TH.InstanceD _ cxt typ decs) =
  ppInstanceHead cxt typ <> line <> indent 2 (vsep (map ppDec decs))
ppDec (TH.FunD name clauses) =
  vsep (map (ppClause name) clauses)
ppDec (TH.PragmaD pragma) = ppPragma pragma
ppDec (TH.SigD name typ) = ppNamePrefix name <+> "::" <+> ppType typ
ppDec d = pretty (TH.pprint d) -- fallback

ppInstanceHead :: TH.Cxt -> TH.Type -> Doc ann
ppInstanceHead cxt typ =
  group $ "instance" <+> ppCxt cxt <> ppType typ <+> "where"

ppCxt :: TH.Cxt -> Doc ann
ppCxt [] = mempty
ppCxt [t] = ppType t <+> "=>" <> softline
ppCxt ts =
  group (encloseSep "(" ")" ", " (map ppType ts))
    <+> "=>"
    <> softline

------------------------------------------------------------
-- Pragmas
------------------------------------------------------------

ppPragma :: TH.Pragma -> Doc ann
ppPragma (TH.InlineP name TH.Inlinable TH.FunLike TH.AllPhases) =
  "{-#" <+> "INLINABLE" <+> ppNamePrefix name <+> "#-}"
ppPragma (TH.InlineP name TH.Inline TH.FunLike TH.AllPhases) =
  "{-#" <+> "INLINE" <+> ppNamePrefix name <+> "#-}"
ppPragma (TH.InlineP name TH.NoInline TH.FunLike TH.AllPhases) =
  "{-#" <+> "NOINLINE" <+> ppNamePrefix name <+> "#-}"
ppPragma p = pretty (TH.pprint (TH.PragmaD p)) -- fallback

------------------------------------------------------------
-- Clauses and matches
------------------------------------------------------------

ppClause :: TH.Name -> TH.Clause -> Doc ann
ppClause name (TH.Clause pats body wheres) =
  group (hang 2 (sep (ppNamePrefix name : map ppPat pats)) <> ppBody body)
    <> ppWheres wheres

ppBody :: TH.Body -> Doc ann
ppBody (TH.NormalB expr) = nest 2 (softline <> "=" <+> ppExp expr)
ppBody (TH.GuardedB guards) = nest 2 (vsep (map ppGuard guards))
  where
    ppGuard (guard', expr) = softline <> "|" <+> ppGuardExp guard' <+> "=" <+> ppExp expr
    ppGuardExp (TH.NormalG e) = ppExp e
    ppGuardExp (TH.PatG stmts) = hsep (map (pretty . TH.pprint) stmts)

ppWheres :: [TH.Dec] -> Doc ann
ppWheres [] = mempty
ppWheres ds = nest 2 (line <> "where" <> line <> vsep (map ppDec ds))

ppMatch :: TH.Match -> Doc ann
ppMatch (TH.Match pat body wheres) =
  group (ppPat pat <> ppBody body) <> ppWheres wheres

------------------------------------------------------------
-- Types
------------------------------------------------------------

ppType :: TH.Type -> Doc ann
ppType (TH.ForallT bndrs cxt typ) =
  "forall" <+> hsep (map ppTyVarBndr bndrs) <> "." <+> ppCxt cxt <> ppType typ
ppType (TH.AppT (TH.AppT TH.ArrowT a) b) =
  ppTypePrec 1 a <+> "->" <+> ppType b
ppType (TH.AppT TH.ListT a) =
  "[" <> ppType a <> "]"
ppType t@(TH.AppT _ _) = ppTypeApp t
ppType (TH.ConT name) = ppName name
ppType (TH.VarT name) = ppName name
ppType TH.ArrowT = "(->)"
ppType (TH.TupleT 0) = "()"
ppType (TH.TupleT n) = "(" <> pretty (replicate (n - 1) ',') <> ")"
ppType TH.ListT = "[]"
ppType (TH.SigT t k) = ppType t <+> "::" <+> ppType k
ppType (TH.ParensT t) = parens (ppType t)
ppType t = pretty (TH.pprint t) -- fallback

ppTypePrec :: Int -> TH.Type -> Doc ann
ppTypePrec p t@(TH.AppT (TH.AppT TH.ArrowT _) _)
  | p > 0 = parens (ppType t)
ppTypePrec p t@(TH.AppT _ _)
  | p >= 2, not (isSingleArgApp t) = parens (ppType t)
ppTypePrec _ t = ppType t

{-| Is this a type application with exactly one argument (e.g. @Maybe a@)?
Single-arg applications at precedence 2 don't need parens. -}
isSingleArgApp :: TH.Type -> Bool
isSingleArgApp (TH.AppT f _) = case f of
  TH.ConT {} -> True
  TH.VarT {} -> True
  _ -> False
isSingleArgApp _ = False

ppTypeApp :: TH.Type -> Doc ann
ppTypeApp t = case collectTypeApps t of
  (TH.TupleT _, args) -> tupled (map ppType args)
  (fun, args) -> group $ nest 2 $ ppType fun <> softline <> sep (map (ppTypePrec 2) args)

collectTypeApps :: TH.Type -> (TH.Type, [TH.Type])
collectTypeApps = go []
  where
    go acc (TH.AppT f a) = go (a : acc) f
    go acc t = (t, acc)

ppTyVarBndr :: TH.TyVarBndr a -> Doc ann
ppTyVarBndr (TH.PlainTV name _) = ppName name
ppTyVarBndr (TH.KindedTV name _ k) = parens (ppName name <+> "::" <+> ppType k)

------------------------------------------------------------
-- Patterns
------------------------------------------------------------

ppPat :: TH.Pat -> Doc ann
ppPat (TH.VarP name) = ppName name
ppPat TH.WildP = "_"
ppPat (TH.ConP name _ pats)
  | null pats = parens (ppNamePrefix name)
  | otherwise =
      parens $
        group $
          nest 2 $
            ppNamePrefix name <> softline <> sep (map ppPat pats)
ppPat (TH.LitP lit) = ppLit lit
ppPat (TH.TupP pats) = tupled (map ppPat pats)
ppPat (TH.BangP pat) = "!" <> ppPat pat
ppPat (TH.ViewP expr pat) = parens (ppExp expr <+> "->" <+> ppPat pat)
ppPat (TH.ParensP pat) = parens (ppPat pat)
ppPat (TH.SigP pat typ) = parens (ppPat pat <+> "::" <+> ppType typ)
ppPat (TH.AsP name pat) = ppName name <> "@" <> ppPat pat
ppPat (TH.InfixP p1 name p2) = ppPat p1 <+> ppName name <+> ppPat p2
ppPat (TH.ListP pats) = list (map ppPat pats)
ppPat p = pretty (TH.pprint p) -- fallback

------------------------------------------------------------
-- Expressions
------------------------------------------------------------

ppExp :: TH.Exp -> Doc ann
ppExp (TH.VarE name) = ppName name
ppExp (TH.ConE name) = ppName name
ppExp (TH.LitE lit) = ppLit lit
ppExp (TH.AppE f x) = ppAppExp f x
ppExp e@TH.InfixE {} = ppInfixExp e
ppExp (TH.LamE pats body) =
  group $ "\\" <> hsep (map ppPat pats) <+> "->" <> nest 2 (softline <> ppExp body)
ppExp (TH.LamCaseE matches) =
  "\\case" <> hardline <> indent 2 (bracesSemiList (map ppMatch matches))
ppExp (TH.CaseE scrut matches) =
  group $
    "case"
      <+> ppExp scrut
      <+> "of"
      <> hardline
      <> indent 2 (bracesSemiList (map ppMatch matches))
ppExp (TH.LetE decs body) =
  group $ "let" <+> align (vsep (map ppDec decs)) <> softline <> "in" <+> ppExp body
ppExp (TH.ListE exprs) = list (map ppExp exprs)
ppExp (TH.TupE mexprs) = tupled (map (maybe mempty ppExp) mexprs)
ppExp (TH.SigE expr typ) = parens (ppExp expr <+> "::" <+> ppType typ)
ppExp (TH.ParensE expr) = parens (ppExp expr)
ppExp e = pretty (TH.pprint e) -- fallback

-- | Pretty-print function application, collecting the spine.
ppAppExp :: TH.Exp -> TH.Exp -> Doc ann
ppAppExp f x =
  case collectApps (TH.AppE f x) of
    (fun, args) -> group $ nest 2 $ ppExpPrec fun <> softline <> sep (map ppExpPrec args)

collectApps :: TH.Exp -> (TH.Exp, [TH.Exp])
collectApps = go []
  where
    go acc (TH.AppE f a) = go (a : acc) f
    go acc e = (e, acc)

-- | Wrap in parens if the expression is a compound form.
ppExpPrec :: TH.Exp -> Doc ann
ppExpPrec e@TH.AppE {} = parens (ppExp e)
ppExpPrec e@TH.InfixE {} = parens (ppExp e)
ppExpPrec e@TH.LamE {} = parens (ppExp e)
ppExpPrec e@TH.LamCaseE {} = parens (ppExp e)
ppExpPrec e@TH.CaseE {} = parens (ppExp e)
ppExpPrec e@TH.LetE {} = parens (ppExp e)
ppExpPrec e = ppExp e

-- | Pretty-print an infix expression, handling chained operators.
ppInfixExp :: TH.Exp -> Doc ann
ppInfixExp (TH.InfixE (Just l) op (Just r)) =
  group $ nest 2 $ ppExpPrec l <> softline <> ppExp op <+> ppInfixRight r
ppInfixExp (TH.InfixE Nothing op (Just r)) =
  parens (ppExp op <+> ppExpPrec r)
ppInfixExp (TH.InfixE (Just l) op Nothing) =
  parens (ppExpPrec l <+> ppExp op)
ppInfixExp e = ppExp e

{-| For the right side of an infix, don't add extra parens if it's the
same infix chain (like nested &&). -}
ppInfixRight :: TH.Exp -> Doc ann
ppInfixRight = ppExpPrec

------------------------------------------------------------
-- Literals
------------------------------------------------------------

ppLit :: TH.Lit -> Doc ann
ppLit (TH.IntegerL n) = pretty n
ppLit (TH.StringL s) = pretty (show s)
ppLit (TH.CharL c) = pretty (show c)
ppLit (TH.RationalL r) = pretty (show r)
ppLit l = pretty (TH.pprint (TH.LitE l)) -- fallback

------------------------------------------------------------
-- Names
------------------------------------------------------------

-- | Render a name. Operators are rendered without parens (for infix use).
ppName :: TH.Name -> Doc ann
ppName name = pretty (TH.pprint name)

-- | Render a name in prefix position. Operators get wrapped in parens.
ppNamePrefix :: TH.Name -> Doc ann
ppNamePrefix name
  | isOperator name = parens (ppName name)
  | otherwise = ppName name

-- | Check if a TH name is an operator (symbol-based, not alphanumeric).
isOperator :: TH.Name -> Bool
isOperator name =
  case TH.nameBase name of
    [] -> False
    (c : _) -> not (isAlphaNum c) && c /= '_'

------------------------------------------------------------
-- Helpers
------------------------------------------------------------

-- | Render items in braces with semicolons (used for case alternatives).
bracesSemiList :: [Doc ann] -> Doc ann
bracesSemiList [] = "{}"
bracesSemiList [d] = "{" <> d <> "}"
bracesSemiList ds = "{" <> concatWith (\a b -> a <> hardline <> " " <> b) ds <> "}"
