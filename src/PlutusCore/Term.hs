{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | The terms of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module PlutusCore.Term where

import PlutusTypes.Type
import Utils.ABT
import Utils.Names
import Utils.Pretty
import Utils.Vars

import qualified Data.ByteString.Lazy as BS
import Data.Functor.Identity
import Data.List (intercalate)

import GHC.Generics





-- | There are ten kinds of terms, declared names @decname[n]@, let
-- expressions @let(e1;x.e2)@, lambdas @lam(x.e)@, application @app(e1;e2)@,
-- constructor terms @con[n](e*)@, case expressions @case(e;c*)@, success
-- expressions @success(e)@, failure expressions @failure@, computation
-- binds @bind(e1;x.e2)@, and finally, built-ins @builtin[n](e*)@.

data TermF r
  = Decname (Sourced String) [Type]
  | Let r r
  | Lam Type r
  | App r r
  | Con String [r]
  | Case [r] [ClauseF r]
  | Success r
  | Failure Type
  | Bind r r
  | PrimData PrimData
  | Builtin String [r]
  deriving (Functor,Foldable,Traversable,Generic)


type Term = ABT TermF


-- | There are three kinds of primitive data in Plutus Core: ints, floats,
-- and byte strings.

data PrimData = PrimInt Int
              | PrimFloat Float
              | PrimByteString BS.ByteString
  deriving (Eq,Generic)


-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause [Scope PatternF] r
  deriving (Functor,Foldable,Traversable,Generic)


type Clause = ClauseF (Scope TermF)


-- | Patterns are only constructor patterns, with some number of pattern args.

data PatternF r = ConPat String [r]
                | PrimPat PrimData
  deriving (Functor,Foldable,Traversable,Generic)

  
type Pattern = ABT PatternF





decnameH :: Sourced String -> [Type] -> Term
decnameH n as = In (Decname n as)

letH :: Term -> String -> Term -> Term
letH m x n = In (Let (scope [] m) (scope [x] n))

lamH :: Type -> String -> Term -> Term
lamH t v b = In (Lam t (scope [v] b))

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

primIntPatH :: Int -> Pattern
primIntPatH x = In (PrimPat (PrimInt x))

primFloatPatH :: Float -> Pattern
primFloatPatH x = In (PrimPat (PrimFloat x))

primByteStringPatH :: BS.ByteString -> Pattern
primByteStringPatH x = In (PrimPat (PrimByteString x))

successH :: Term -> Term
successH m = In (Success (scope [] m))

failureH :: Type -> Term
failureH t = In (Failure t)

bindH :: Term -> String -> Term -> Term
bindH m x n = In (Bind (scope [] m) (scope [x] n))

primIntH :: Int -> Term
primIntH x = In (PrimData (PrimInt x))

primFloatH :: Float -> Term
primFloatH x = In (PrimData (PrimFloat x))

primByteStringH :: BS.ByteString -> Term
primByteStringH x = In (PrimData (PrimByteString x))

builtinH :: String -> [Term] -> Term
builtinH n ms = In (Builtin n (map (scope []) ms))





substTypeMetas :: [(MetaVar,Type)] -> Term -> Term
substTypeMetas subs x0 = runIdentity (go x0)
  where
    go :: Term -> Identity Term
    go (Var x) = return (Var x)
    go (In (Decname n ts)) =
      return (In (Decname n (map (substMetas subs) ts)))
    go (In (Lam t sc)) = (In . Lam (substMetas subs t)) <$> underF go sc
    go (In (Failure t)) = return (In (Failure (substMetas subs t)))
    go (In x) = In <$> traverse (underF go) x


substTypeMetasClause :: [(MetaVar,Type)] -> Clause -> Clause
substTypeMetasClause subs (Clause ps sc) =
  Clause ps (under (substTypeMetas subs) sc)









-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]

  parenRec (Var v) =
    name v
  parenRec (In (Decname n as)) =
    "defined[" ++ showSourced n
      ++ ";"
      ++ intercalate "," (map pretty as)
      ++ "]"
  parenRec (In (Let m n)) =
    "let("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ head (names n) ++ "." ++ parenthesize Nothing (body n)
    ++ ")"
  parenRec (In (Lam t sc)) =
    "\\(" ++ pretty t ++ ";"
      ++ unwords (names sc)
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
  parenRec (In (Failure t)) =
    "failure(" ++ pretty t ++ ")"
  parenRec (In (Bind m sc)) =
    "bind("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ unwords (names sc)
    ++ "."
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (PrimData (PrimInt x))) =
    "int[" ++ show x ++ "]"
  parenRec (In (PrimData (PrimFloat x))) =
    "float[" ++ show x ++ "]"
  parenRec (In (PrimData (PrimByteString x))) =
    "byteString[" ++ prettyByteString x ++ "]"
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
  parenRec (In (PrimPat (PrimInt x))) =
    "primPat[int[" ++ show x ++ "]]"
  parenRec (In (PrimPat (PrimFloat x))) =
    "primPat[float[" ++ show x ++ "]]"
  parenRec (In (PrimPat (PrimByteString x))) =
    "primPat[byteString[" ++ prettyByteString x ++ "]]"