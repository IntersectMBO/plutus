{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | The terms of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module PlutusCore.Term where

import Utils.ABT
import Utils.Pretty

import Data.List (intercalate)





-- | There are five kinds of terms, an annotated term @M : T@, a lambda term
-- @\\x -> M@, an application term @M N@, a constructor term @C M0 ... Mn@, and
-- a case term @case M0 || ... || Mn of p0* -> N0 | ... | pm* -> Nm end@.

data TermF r
  = Defined String
  | Let r r
  | Lam r
  | App r r
  | Con String [r]
  | Case r [ClauseF r]
  | Success r
  | Failure
  | Bind r r
  | Builtin String [r]
  deriving (Functor,Foldable)


type Term = ABT TermF


-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause (Scope PatternF) r
  deriving (Functor,Foldable)


type Clause = ClauseF (Scope TermF)


-- | Patterns are only constructor patterns, with some number of pattern args.

data PatternF r = ConPat String [r]
  deriving (Functor,Foldable,Traversable)

  
type Pattern = ABT PatternF


-- | Programs are collections of declarations.

newtype Program = Program [Declaration]


-- | Declarations are just names with definitions.

data Declaration = Declaration String Term



defined :: String -> Term
defined n = In (Defined n)

letH :: Term -> String -> Term -> Term
letH m x n = In (Let (scope [] m) (scope [x] n))

lamH :: String -> Term -> Term
lamH v b = In (Lam (scope [v] b))

appH :: Term -> Term -> Term
appH f x = In (App (scope [] f) (scope [] x))

conH :: String -> [Term] -> Term
conH c xs = In (Con c (map (scope []) xs))

caseH :: Term -> [Clause] -> Term
caseH a cs = In (Case (scope [] a) cs)

clauseH :: [String] -> Pattern -> Term -> Clause
clauseH vs p b = Clause (scope vs p) (scope vs b)

conPatH :: String -> [Pattern] -> Pattern
conPatH c xs = In (ConPat c (map (scope []) xs))

successH :: Term -> Term
successH m = In (Success (scope [] m))

failureH :: Term
failureH = In Failure

bindH :: Term -> String -> Term -> Term
bindH m x n = In (Bind (scope [] m) (scope [x] n))

builtinH :: String -> [Term] -> Term
builtinH n ms = In (Builtin n (map (scope []) ms))









-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]

  parenRec (Var v) =
    name v
  parenRec (In (Defined n)) = "defined[" ++ n ++ "]"
  parenRec (In (Let m n)) =
    "let("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ parenthesize Nothing (instantiate0 n)
    ++ ")"
  parenRec (In (Lam sc)) =
    "\\(" ++ unwords (names sc)
      ++ "."
      ++ parenthesize Nothing (body sc)
      ++ ")"
  parenRec (In (App f a)) =
    "app("
      ++ parenthesize Nothing (instantiate0 f)
      ++ ";"
      ++ parenthesize Nothing (instantiate0 a)
      ++ ")"
  parenRec (In (Con c as)) =
    "con[" ++ c ++ "]("
      ++ intercalate
           ";"
           (map (parenthesize Nothing . instantiate0) as)
      ++ ")"
  parenRec (In (Case a cs)) =
    "case("
      ++ parenthesize Nothing (body a)
      ++ ";"
      ++ intercalate "," (map auxClause cs)
      ++ ")"
    where
      auxClause :: Clause -> String
      auxClause (Clause p sc) =
        "cl("
        ++ parenthesize Nothing (body p)
        ++ ";"
        ++ parenthesize Nothing (body sc)
        ++ ")"
  parenRec (In (Success m)) =
    "success("
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In Failure) =
    "failure"
  parenRec (In (Bind m sc)) =
    "bind("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ unwords (names sc)
    ++ "."
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (Builtin n ms)) =
    "buildin[" ++ n ++ "]("
      ++ intercalate "," (map (parenthesize Nothing . instantiate0) ms)
      ++ ")"





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