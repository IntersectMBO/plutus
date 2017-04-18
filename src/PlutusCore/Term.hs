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
import Utils.JSABT
import Utils.Names
import Utils.Pretty
import Utils.Vars

import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BSChar8
import Data.Functor.Identity
import Data.List (intercalate)

import GHC.Generics hiding (Constructor)





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
  | Case r [ClauseF r]
  | Success r
  | Failure
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



-- | A `Constructor` is either just a `String` that names the constructor
-- for a user-defined type, or a `PrimData`.

data SimplePattern = VarPat String | ConPat String
  deriving (Generic)




-- | Clauses are a component of terms that have bunch of pattern scopes
-- together with a clause body.

data ClauseF r = Clause SimplePattern r
  deriving (Functor,Foldable,Traversable,Generic)


type Clause = ClauseF (Scope TermF)






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

caseH :: Term -> [Clause] -> Term
caseH a cs = In (Case (scope [] a) cs)

clauseH :: SimplePattern -> [String] -> Term -> Clause
clauseH p vs b = Clause p (scope vs b)

successH :: Term -> Term
successH m = In (Success (scope [] m))

failureH :: Term
failureH = In Failure

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






prettyPrimData :: PrimData -> String
prettyPrimData (PrimInt x) =
  "int[" ++ show x ++ "]"
prettyPrimData (PrimFloat x) =
  "float[" ++ show x ++ "]"
prettyPrimData (PrimByteString x) =
  "byteString[" ++ prettyByteString x ++ "]"



-- | Terms have a variety of locations that can potentially be sites of
-- de-parenthesization.

instance Parens Term where
  type Loc Term = ()
  
  parenLoc _ = [()]

  parenRec (Var v) =
    name v
  parenRec (In (Decname n)) =
    "defined[" ++ showSourced n
      ++ "]"
  parenRec (In (Let m n)) =
    "let("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ head (names n) ++ "." ++ parenthesize Nothing (body n)
    ++ ")"
  parenRec (In (Lam sc)) =
    "\\("
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
  parenRec (In (Case a cs)) =
    "case("
      ++ parenthesize Nothing (body a)
      ++ ";"
      ++ intercalate "," (map auxClause cs)
      ++ ")"
    where
      auxPat :: SimplePattern -> String
      auxPat (VarPat x) = x
      auxPat (ConPat c) = c
      
      auxClause :: Clause -> String
      auxClause (Clause con sc) =
        "cl("
        ++ auxPat con
        ++ ";"
        ++ intercalate "," (names sc)
        ++ "."
        ++ parenthesize Nothing (body sc)
        ++ ")"
  parenRec (In (Success m)) =
    "success("
      ++ parenthesize Nothing (instantiate0 m)
      ++ ")"
  parenRec (In Failure ) =
    "failure()"
  parenRec (In (Bind m sc)) =
    "bind("
    ++ parenthesize Nothing (instantiate0 m)
    ++ ";"
    ++ unwords (names sc)
    ++ "."
    ++ parenthesize Nothing (body sc)
    ++ ")"
  parenRec (In (PrimData pd)) = prettyPrimData pd
  parenRec (In (Builtin n ms)) =
    "buildin[" ++ n ++ "]("
      ++ intercalate "," (map (parenthesize Nothing . instantiate0) ms)
      ++ ")"







instance ToJS Term where
  toJS m0 = fst (runState (go m0) (0,[]))
    where
      getVar :: Int -> State (Int,[String]) String
      getVar i =
        do (_,ctx) <- get
           return (ctx !! i)
      
      withVar :: (String -> State (Int,[String]) a) -> State (Int,[String]) (String,a)
      withVar f =
        do (i,ctx) <- get
           let x = "x" ++ show i
           put (i+1, x : ctx)
           a <- f x
           (i',_) <- get
           put (i',ctx)
           return (x,a)
      
      withVars :: Int -> ([String] -> State (Int,[String]) a) -> State (Int,[String]) ([String],a)
      withVars n f =
        do (i,ctx) <- get
           let xs = [ "x" ++ show j | j <- [i..i+n-1] ]
           put (i+n, xs ++ ctx)
           a <- f xs
           put (i+n, ctx)
           return (xs,a)
      
      go :: Term -> State (Int,[String]) JSABT
      go (Var (Free _)) =
        error "There should never be free vars in a JS-able term."
      go (Var (Bound _ (BoundVar i))) =
        do x <- getVar i
           return (JSVar x)
      go (Var (Meta _)) =
        error "There should never be meta vars in a JS-able term."
      go (In (Decname n)) =
        return $ JSABT "Decname" [JSString (showSourced n)]
      go (In (Let m sc)) =
        do m' <- go (instantiate0 m)
           (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Let" [m', JSScope [x] b]
      go (In (Lam sc)) =
        do (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Lam" [JSScope [x] b]
      go (In (App f x)) =
        do f' <- go (instantiate0 f)
           x' <- go (instantiate0 x)
           return $ JSABT "App" [f',x']
      go (In (Con c ms)) =
        do ms' <- mapM (go . instantiate0) ms
           return $ JSABT "Con" [JSString c, JSArray ms']
      go (In (Case m cs)) =
        do m' <- go (instantiate0 m)
           cs' <- mapM goClause cs
           return $ JSABT "Case" [m', JSArray cs']
      go (In (Success m)) =
        do m' <- go (instantiate0 m)
           return $ JSABT "Success" [m']
      go (In Failure) =
        return $ JSABT "Failure" []
      go (In (Bind m sc)) =
        do m' <- go (instantiate0 m)
           (x,b) <- withVar $ \_ -> go (body sc)
           return $ JSABT "Bind" [m', JSScope [x] b]
      go (In (PrimData pd)) =
        do pd' <- goPrimData pd
           return $ JSABT "PrimData" [pd']
      go (In (Builtin n ms)) =
        do ms' <- mapM (go . instantiate0) ms
           return $ JSABT "Builtin" [JSString n, JSArray ms']
      
      goPrimData :: PrimData -> State (Int,[String]) JSABT
      goPrimData (PrimInt i) =
        return $ JSABT "PrimInt" [JSInt i]
      goPrimData (PrimFloat f) =
        return $ JSABT "PrimFloat" [JSFloat f]
      goPrimData (PrimByteString bs) =
        return $ JSABT "PrimByteString" [JSString (BSChar8.unpack bs)]
      
      goClause :: Clause -> State (Int,[String]) JSABT
      goClause (Clause c sc) =
        do p' <- goSimplePattern c
           (xs, b) <- withVars (length (names sc)) $ \_ ->
                        go (body sc)
           return $ JSABT "Clause" [p', JSScope xs b]
      
      goSimplePattern :: SimplePattern -> State (Int,[String]) JSABT
      goSimplePattern (VarPat x) =
        return $ JSABT "VarPat" [JSString x]
      goSimplePattern (ConPat c) =
        return $ JSABT "ConPat" [JSString c]
