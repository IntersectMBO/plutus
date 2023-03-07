-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module AlgTypes where

import Data.Set qualified as S
import Language.LBNF

-------------------------------------
-- Parser for Algebraic Data Types --
-------------------------------------

-- has a ton of shift-reduce conflicts, so you need to use a ton of parentheses sometimes to get it
-- to parse the type you want. Neat the top of the TODO list for this is getting rid of the shift-reduce
-- conflicts.

bnfc [lbnf|

TOne.  TyExp ::= "1" ;
TZero. TyExp ::= "0" ;
TProd. TyExp ::= TyExp "*" TyExp ;
TSum.  TyExp ::= TyExp "+" TyExp ;
TVar.  TyExp ::= Ident ;
TAll.  TyExp ::= "all" Ident "." TyExp ;
TAbs.  TyExp ::= "lam" Ident "." TyExp ;
TApp.  TyExp ::= TyExp TyExp ;
TFun.  TyExp ::= TyExp " -> " TyExp ;
_.     TyExp ::= "(" TyExp ")" ;


KStar. KindExp ::= "*" ;
KArr.  KindExp ::= KindExp "->" KindExp ;

TyDecl. DeclExp ::= Ident  "=" TyExp ;

terminator DeclExp ";" ;

entrypoints TyExp, KindExp, DeclExp;
 |]

type VarName = String

data AlgType where
  One  :: AlgType
  Zero :: AlgType
  Prod :: AlgType -> AlgType -> AlgType
  Sum  :: AlgType -> AlgType -> AlgType
  Var  :: VarName -> AlgType
  All  :: VarName -> AlgType -> AlgType
  Abs  :: VarName  -> AlgType -> AlgType
  App  :: AlgType -> AlgType -> AlgType
  Fun  :: AlgType -> AlgType -> AlgType
  Mu   :: VarName -> AlgType -> AlgType -- not in grammar, but accessible through x = t(x) in declarations.
  -- Should Mu require kind annotation? If so, what are the kinds?

instance Show AlgType where
  show One          = "1"
  show Zero         = "0"
  show (Var x)      = x
  show (Prod t1 t2) = (show t1) ++ " * " ++ (show t2)
  show (Sum  t1 t2) = (show t1) ++ " + " ++ (show t2)
  show (App t1 t2)  = (show t1) ++ " " ++ (show t2)
  show (All x t)    = "(all " ++ x ++ " . " ++ (show t) ++ ")"
  show (Abs x t)    = "(lam " ++ x ++ " . " ++ (show t) ++ ")"
  show (Mu x t)     = "(mu " ++ x ++ "." ++ (show t) ++ ")"
  show (Fun t1 t2)  = (show t1) ++ " -> " ++ (show t2)

prettyKindExp :: KindExp -> String
prettyKindExp KStar        = "*"
prettyKindExp (KArr k1 k2) = (prettyKindExp k1) ++ "->" ++ (prettyKindExp k2)

algType :: TyExp -> AlgType
algType TOne               = One
algType TZero              = Zero
algType (TProd t1 t2)      = Prod (algType t1) (algType t2)
algType (TSum  t1 t2)      = Sum  (algType t1) (algType t2)
algType (TVar (Ident x))   = Var x
algType (TAll (Ident x) t) = All x (algType t)
algType (TAbs (Ident x) t) = Abs x (algType t)
algType (TApp t1 t2)       = App (algType t1) (algType t2)
algType (TFun t1 t2)       = Fun (algType t1) (algType t2)

algDecl :: DeclExp -> Decl AlgType
algDecl (TyDecl (Ident name) t) = Decl name (algType t)

-- Problem: names in signature must be unique for this to work, we don't currently check this.
data Decl a = Decl String a

instance Eq (Decl a) where
  (Decl x _) == (Decl y _) = x == y

instance Ord (Decl a) where
  compare (Decl x _) (Decl y _) = compare x y

type AlgSignature = S.Set (Decl AlgType)

algSignature :: [Decl AlgType] -> AlgSignature
algSignature ds = S.fromList ds

prettySignature :: (Show a) => S.Set (Decl a) -> IO ()
prettySignature sig = mapM_ (putStrLn . show) (S.toList sig)

instance (Show a) => Show (Decl a) where
  show (Decl x t) = x ++ " = " ++ (show t)

-- free variables
free :: AlgType -> S.Set VarName
free One          = S.empty
free Zero         = S.empty
free (Prod t1 t2) = S.union (free t1) (free t2)
free (Sum  t1 t2) = S.union (free t1) (free t2)
free (Var x)      = S.singleton x
free (All x t)    = S.delete x (free t)
free (Abs x t)    = S.delete x (free t)
free (App t1 t2)  = S.union (free t1) (free t2)
free (Mu x t)     = S.delete x (free t)
free (Fun t1 t2)  = S.union (free t1) (free t2)

-- sub x t a is a[t/x], the result of substituting t for free occurrences of x in a.
-- I suspect the way this is implemented is a bit dumb. I don't think it impacts performance.
sub :: AlgType -> VarName -> AlgType -> AlgType
sub t x a = subExcept [] t x a
  where
  subExcept :: [VarName] -> AlgType -> VarName -> AlgType -> AlgType
  subExcept bound t x t' =
    if x `elem` bound then t'
    else case t' of
           One          -> One
           Zero         -> Zero
           (Var y)      -> if x == y then t else t'
           (Prod t1 t2) -> Prod (subExcept bound t x t1) (subExcept bound t x t2)
           (Sum  t1 t2) -> Sum  (subExcept bound t x t1) (subExcept bound t x t2)
           (App  t1 t2) -> App  (subExcept bound t x t1) (subExcept bound t x t2)
           (Abs y t')   -> Abs y (subExcept (y:bound) t x t')
           (All y t')   -> All y (subExcept (y:bound) t x t')
           (Mu y t')    -> Mu y (subExcept (y:bound) t x t')
           (Fun t1 t2)  -> Fun (subExcept bound t x t1) (subExcept bound t x t2)

-- rewrite x+0 => x, x+1 => x.
simplify :: AlgType -> AlgType
simplify One = One
simplify Zero = Zero
simplify (Prod t1 t2) = let s1 = simplify t1
                            s2 = simplify t2 in
                          case s1 of
                            One -> s2
                            _   -> case s2 of
                                     One -> s1
                                     _   -> Prod s1 s2
simplify (Sum t1 t2) = let s1 = simplify t1
                           s2 = simplify t2 in
                         case s1 of
                           Zero -> s2
                           _    -> case s2 of
                                     Zero -> s1
                                     _    -> Sum s1 s2
simplify (Var x) = Var x
simplify (All x t) = All x (simplify t)
simplify (Abs x t) = Abs x (simplify t)
simplify (App t1 t2) = App (simplify t1) (simplify t2)
simplify (Fun t1 t2) = Fun (simplify t1) (simplify t2)
simplify (Mu x t) = Mu x (simplify t)

simplifySignature :: AlgSignature -> AlgSignature
simplifySignature = S.map (\(Decl name t) -> Decl name (simplify t))

