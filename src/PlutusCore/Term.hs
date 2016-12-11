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
import Utils.Names
import Utils.Pretty

import Data.List (intercalate)






-- | There are ten kinds of terms, declared names @decname[n]@, let
-- expressions @let(e1;x.e2)@, lambdas @lam(x.e)@, application @app(e1;e2)@,
-- constructor terms @con[n](e*)@, case expressions @case(e;c*)@, success
-- expressions @success(e)@, failure expressions @failure@, computation
-- binds @bind(e1;x.e2)@, and finally, built-ins @builtin[n](e*)@.

data TermF r
  = Decname (Sourced String)
  | Let r r
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


-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause [Scope PatternF] r
  deriving (Functor,Foldable)


type Clause = ClauseF (Scope TermF)


-- | Patterns are only constructor patterns, with some number of pattern args.

data PatternF r = ConPat String [r]
  deriving (Functor,Foldable,Traversable)

  
type Pattern = ABT PatternF





decnameH :: Sourced String -> Term
decnameH n = In (Decname n)

letH :: Term -> String -> Term -> Term
letH m x n = In (Let (scope [] m) (scope [x] n))

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
  parenRec (In (Decname n)) = "defined[" ++ showSourced n ++ "]"
  parenRec (In (Let m n)) =
    "let("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ head (names n) ++ "." ++ parenthesize Nothing (body n)
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
  parenRec (In (Case as cs)) =
    "case("
      ++ intercalate "," (map (parenthesize Nothing . body) as)
      ++ ";"
      ++ intercalate "," (map auxClause cs)
      ++ ")"
    where
      auxClause :: Clause -> String
      auxClause (Clause ps sc) =
        "cl("
        ++ intercalate "," (map (parenthesize Nothing . body) ps)
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

instance Parens Pattern where
  type Loc Pattern = ()
  
  parenLoc _ = [()]
  
  parenRec (Var v) =
    name v
  parenRec (In (ConPat c ps)) =
    "conPat[" ++ c ++ "]("
      ++ intercalate "," (map (parenthesize Nothing . body) ps)
      ++ ")"