{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE ImportQualifiedPost #-}
-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.Exp(
  Exp(..),
  PrimOp,
  substExp,
  app2, app3,
  allVarsExp, freeVars,
  lams, apps,
  foobar, toposort,
  toUPLC
  ) where
import Data.Char
import Data.List
import Debug.Trace
import MHSPrelude hiding ((<>))
import MicroHs.Expr (Lit (..), showLit)
import MicroHs.Ident
import MicroHs.List
import Prelude qualified ()
import Text.PrettyPrint.HughesPJLite

import UntypedPlutusCore qualified as UPLC

type PrimOp = String

data Exp
  = Var Ident
  | App Exp Exp
  | Lam Ident Exp
  | Lit Lit
  deriving (Eq)

instance NFData Exp where
  rnf (Var a)   = rnf a
  rnf (App a b) = rnf a `seq` rnf b
  rnf (Lam a b) = rnf a `seq` rnf b
  rnf (Lit a)   = rnf a

app2 :: Exp -> Exp -> Exp -> Exp
app2 f a1 a2 = App (App f a1) a2

app3 :: Exp -> Exp -> Exp -> Exp -> Exp
app3 f a1 a2 a3 = App (app2 f a1 a2) a3

instance Show Exp where
  show = render . ppExp

toUPLC :: Exp -> UPLC.Term UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
toUPLC e = go [] e
  where
    getIdx :: (Eq a, Show a) => [a] -> a -> UPLC.Index
    getIdx (x:xs) y
      | x == y = 1
      | otherwise = 1 + getIdx xs y
    getIdx _ y = trace (show y) $ error ""
    -- assumes names are unique
    go binds (Lam ident x) = UPLC.LamAbs () (UPLC.DeBruijn $ 0) (go (ident:binds) x)
    go binds (Var ident)   = UPLC.Var () (UPLC.DeBruijn $ getIdx binds ident)
    go binds (App a b)     = UPLC.Apply () (go binds a) (go binds b)
    go _binds (Lit _a)     = UPLC.Error ()

usedIdent :: [Ident] -> Exp -> [Ident]
usedIdent knownIdent (Var ident) = if elem ident knownIdent then [ident] else []
usedIdent knownIdent (App e1 e2) = (usedIdent knownIdent e1) ++ (usedIdent knownIdent e2)
usedIdent knownIdent (Lam _ e)   = usedIdent knownIdent e
usedIdent _knownIdent (Lit _)    = []

foobar :: [(Ident, Exp)] -> Ident -> Maybe Exp
foobar table entryPoint =
  case filter ((== entryPoint) . fst) table of
    [] -> Nothing
    ((_, entryPointExp):_) ->
      let
        knownIdent = (fst <$> table)
        tableSorted = toposort table
        getReqs = usedIdents knownIdent
        allReqs (ident, exp) = ident : getReqs exp
      in pure $ go tableSorted (usedIdent knownIdent entryPointExp) entryPointExp

toposort :: [(Ident, Exp)] -> [(Ident, Exp)]
toposort table = go givenDeps
  where
    knownIdent = (fst <$> table)
    givenDeps :: [((Ident, Exp), [Ident])]
    givenDeps = nub $ (\(a, b) -> ((a, b), filter (/= a) $ usedIdent knownIdent b)) <$> table

    removeDep :: Ident -> [((Ident, Exp), [Ident])] -> [((Ident, Exp), [Ident])]
    removeDep ident deps =
      fmap (\(e, d) -> (e, filter (/= ident) d)) deps

    go deps =
      case filter (null . snd) deps of
        []                    -> []
        ((e@(ident, _), _):_) -> e : go (removeDep ident $ filter ((/= ident) . fst . fst) deps)

ppExp :: Exp -> Doc
ppExp ae =
  case ae of
--    Let i e b -> sep [ text "let" <+> ppIdent i <+> text "=" <+> ppExp e, text "in" <+> ppExp b ]
    Var i   -> ppIdent i
    App f a -> parens $ ppExp f <+> ppExp a
    Lam i e -> parens $ text "\\" <> ppIdent i <> text "." <+> ppExp e
    Lit l   -> text (showLit l)

substExp :: Ident -> Exp -> Exp -> Exp
substExp si se ae =
  case ae of
    Var i -> if i == si then se else ae
    App f a -> App (substExp si se f) (substExp si se a)
    Lam i e -> if si == i then
                 ae
               else if i `elem` freeVars se then
                 let
                   fe = allVarsExp e
                   ase = allVarsExp se
                   j = head [ v | n <- enumFrom (0::Int),
                              let { v = mkIdent ("a" ++ show n) },
                              v `notElem` ase, v `notElem` fe, v /= si ]
                 in
                   --trace ("substExp " ++ show [si, i, j]) $
                   Lam j (substExp si se (substExp i (Var j) e))
               else
                   Lam i (substExp si se e)
    Lit _ -> ae

-- This naive freeVars seems to be the fastest.
freeVars :: Exp -> [Ident]
freeVars ae =
  case ae of
    Var i   -> [i]
    App f a -> freeVars f ++ freeVars a
    Lam i e -> deleteAllBy (==) i (freeVars e)
    Lit _   -> []

allVarsExp :: Exp -> [Ident]
allVarsExp ae =
  case ae of
    Var i   -> [i]
    App f a -> allVarsExp f ++ allVarsExp a
    Lam i e -> i : allVarsExp e
    Lit _   -> []

lams :: [Ident] -> Exp -> Exp
lams xs e = foldr Lam e xs

apps :: Exp -> [Exp] -> Exp
apps f = foldl App f
