{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}







module Plutus.Term where

import Plutus.Type

import Utils.ABT
import Utils.Pretty
import Utils.Vars

import Data.List (intercalate)





-- | There are twelve kinds of terms

data TermF r
  = Decname String
  | Ann r Type
  | Let Type r r
  | Lam r
  | App r r
  | Con String [r]
  | Case [r] [ClauseF r]
  | Success r
  | Failure
  | Bind r r
  | Builtin String [r]
  deriving (Functor,Foldable)


type Term = ABT TermF


-- | A Term Declaration is just a name with a type and  some defining clauses.

data LetDeclF r
  = LetDeclTerm String Type r
  | LetDeclClauses String Type [LetClauseF r]
  deriving (Functor,Foldable)

type LetDecl = LetDeclF (Scope TermF)


-- | A Term Clause is some patterns together with a clause body term.

data LetClauseF r
  = LetClause [Scope PatternF] r
  deriving (Functor,Foldable)

type LetClause = LetClauseF (Scope TermF)


-- | Clauses are a subsort of terms that has bunch of pattern scopes together
-- with a clause body.

data ClauseF r = Clause [Scope PatternF] r
  deriving (Functor,Foldable)


type Clause = ClauseF (Scope TermF)


-- | Patterns are only constructor patterns, with some number of pattern args.

data PatternF r = ConPat String [r]
  deriving (Functor,Foldable,Traversable)

  
type Pattern = ABT PatternF


decnameH :: String -> Term
decnameH n = In (Decname n)

annH :: Term -> Type -> Term
annH m t = In (Ann (scope [] m) t)

letClauseH :: [String] -> [Pattern] -> Term -> LetClause
letClauseH vs ps b = LetClause (map (scope vs) ps) (scope vs b)

letH :: [LetDecl] -> Term -> Term
letH tmds n0 =
  helperFold
    (\(x,a,m) n' -> In (Let a (scope [] m) (scope [x] n')))
    (map desugarLetDecl tmds)
    n0
  where
    desugarLetDecl :: LetDecl -> (String, Type, Term)
    desugarLetDecl (LetDeclTerm n a m) =
      (n,a,instantiate0 m)
    desugarLetDecl (LetDeclClauses n a cs) =
      case cs of
        [] -> error "Empty let declarations should not exist."
        [LetClause pscs sc] | all isVarPat (map body pscs) ->
          let xs = names sc
              b = body sc
          in (n, a, helperFold lamH xs b)
        LetClause pscs0 _:_ ->
          let clauses = [ Clause pscs sc | LetClause pscs sc <- cs ]
              xs0 = [ "x" ++ show i
                    | i <- [0..length pscs0 - 1]
                    ]
          in ( n
             , a
             , helperFold
                 lamH
                 xs0
                 (caseH (map (Var . Free . FreeVar) xs0) clauses)
             )
    
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False

lamH :: String -> Term -> Term
lamH v b = In (Lam (scope [v] b))

appH :: Term -> Term -> Term
appH f x = In (App (scope [] f) (scope [] x))

conH :: String -> [Term] -> Term
conH c xs = In (Con c (map (scope []) xs))

caseH :: [Term] -> [Clause] -> Term
caseH as cs = In (Case (map (scope []) as) cs)

clauseH :: [String] -> [Pattern] -> Term -> Clause
clauseH vs ps b = Clause (map (scope vs) ps) (scope vs b)

conPatH :: String -> [Pattern] -> Pattern
conPatH c xs = In (ConPat c (map (scope []) xs))

successH :: Term -> Term
successH m = In (Success (scope [] m))

failureH :: Term
failureH = In Failure

bindH :: String -> Term -> Term -> Term
bindH x m n = In (Bind (scope [] m) (scope [x] n))

builtinH :: String -> [Term] -> Term
builtinH n ms = In (Builtin n (map (scope []) ms))





-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

data TermParenLoc
  = AnnTerm
  | LetArg | LetBody
  | LamBody | AppFun | AppArg
  | ConArg | CaseArg | ClauseBody
  | BindArg | BindBody
  deriving (Eq)


instance Parens Term where
  type Loc Term = TermParenLoc
  
  parenLoc (Var _) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,AppArg,ConArg,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Decname _)) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,AppArg,ConArg,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Ann _ _)) =
    [LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Let _ _ _)) =
    [LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Lam _)) =
    [LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (App _ _)) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Con _ [])) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,AppArg,ConArg,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Con _ _)) =
    [AnnTerm,LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Case _ _)) =
    [LetArg,LetBody,LamBody,ClauseBody,BindArg,BindBody]
  parenLoc (In (Success _)) =
    [AnnTerm,LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In Failure) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,AppArg,ConArg,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Bind _ _)) =
    [LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Builtin _ [])) =
    [AnnTerm,LetArg,LetBody,LamBody,AppFun,AppArg,ConArg,CaseArg,ClauseBody,BindArg,BindBody]
  parenLoc (In (Builtin _ _)) =
    [AnnTerm,LetArg,LetBody,LamBody,CaseArg,ClauseBody,BindArg,BindBody]
    

  parenRec (Var v) =
    name v
  parenRec (In (Decname n)) = n
  parenRec (In (Ann m t)) =
    parenthesize (Just AnnTerm) (instantiate0 m)
      ++ " : "
      ++ pretty t
  parenRec (In (Let a m sc)) =
    "let " ++ head (names sc) ++ " : "
      ++ pretty a
      ++ " { "
      ++ head (names sc)
      ++ " = "
      ++ parenthesize (Just LetArg) (instantiate0 m)
      ++ " } in "
      ++ parenthesize (Just LetBody) (body sc)
  parenRec (In (Lam sc)) =
    "\\" ++ unwords (names sc)
      ++ " -> "
      ++ parenthesize (Just LamBody)
           (body sc)
  parenRec (In (App f a)) =
    parenthesize (Just AppFun) (instantiate0 f)
      ++ " "
      ++ parenthesize (Just AppArg) (instantiate0 a)
  parenRec (In (Con c [])) =
    c
  parenRec (In (Con c as)) =
    c ++ " "
      ++ intercalate
           " "
           (map (parenthesize (Just ConArg) . instantiate0) as)
  parenRec (In (Case as cs)) =
    "case "
      ++ intercalate
           " || "
           (map (parenthesize (Just CaseArg) . instantiate0) as)
      ++ " of "
      ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause :: Clause -> String
      auxClause (Clause pscs sc) =
        intercalate " || "
          (map (parenthesize Nothing . body) pscs)
        ++ " -> "
        ++ parenthesize (Just ClauseBody) (body sc)
  parenRec (In (Success m)) =
    "success "
      ++ parenthesize (Just ConArg) (instantiate0 m)
  parenRec (In Failure) =
    "failure"
  parenRec b@(In (Bind _ _)) =
    "do { "
      ++ intercalate " ; "
           [ x ++ " <- " ++ parenthesize (Just BindArg) m
           | (x,m) <- xms
           ]
      ++ " ; "
      ++ parenthesize (Just BindBody) n0
      ++ " }"
    where
      (xms,n0) = gatherBinds b
      
      gatherBinds :: Term -> ([(String, Term)], Term)
      gatherBinds (In (Bind m sc)) =
        let (rs,n) = gatherBinds (body sc)
        in ((head (names sc), instantiate0 m):rs, n)
      gatherBinds n = ([], n)
  parenRec (In (Builtin n ms)) =
    "!" ++ n ++ " "
      ++ intercalate
           " "
           (map (parenthesize (Just AppArg) . instantiate0) ms)





-- | Pattern locations are even simpler, as there's only one: constructor arg.

data PatternParenLoc = ConPatArg
  deriving (Eq)

instance Parens Pattern where
  type Loc Pattern = PatternParenLoc
  
  parenLoc (Var _)            = [ConPatArg]
  parenLoc (In (ConPat _ [])) = [ConPatArg]
  parenLoc (In (ConPat _ _))  = []
  
  parenRec (Var v) =
    name v
  parenRec (In (ConPat c [])) = c
  parenRec (In (ConPat c ps)) =
    c ++ " " ++ unwords (map (parenthesize (Just ConPatArg) . body) ps)