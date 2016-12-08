{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | This module defines how to evaluate terms in the simply typed lambda
-- calculus w/ non-parametric user defined types (eg Bool, Nat).

module PlutusCore.Evaluation where

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Names
import Utils.Pretty (pretty)
import PlutusCore.Term

import Control.Monad.Except
import Control.Monad.Reader (runReaderT)





-- | Pattern matching for case expressions.

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (Var _) v = Just [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM matchPattern (map body ps) (map body as))
matchPattern _ _ = Nothing

matchPatterns :: [Pattern] -> [Term] -> Maybe [Term]
matchPatterns ps zs = fmap concat (zipWithM matchPattern ps zs)

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause pscs sc:cs) vs =
  case matchPatterns (map body pscs) vs of
    Nothing -> matchClauses cs vs
    Just xs -> Just (instantiate sc xs)





-- | Standard eager evaluation.

instance Eval (Env (Sourced String) Term) Term where
  eval (Var v) =
    return $ Var v
  eval (In (Decname x)) =
    do env <- environment
       case lookup x env of
         Nothing -> throwError $ "Unknown constant/defined term: "
                              ++ showSourced x
         Just m  -> return m
  eval (In (Let m sc)) =
    do em <- eval (instantiate0 m)
       eval (instantiate sc [em])
  eval (In (Lam sc)) =
    return $ In (Lam sc)
  eval (In (App f a)) =
    do ef <- eval (instantiate0 f)
       ea <- eval (instantiate0 a)
       case ef of
         In (Lam sc) -> eval (instantiate sc [ea])
         _ -> return $ appH ef ea
  eval (In (Con c as)) =
    do eas <- mapM (eval . instantiate0) as
       return $ conH c eas
  eval (In (Case ms cs)) =
    do ems <- mapM (eval . instantiate0) ms
       case matchClauses cs ems of
         Nothing -> throwError $ "Incomplete pattern match: " ++ pretty (In (Case ms cs))
         Just b  -> eval b
  eval (In (Success m)) =
    do em <- eval (instantiate0 m)
       return $ successH em
  eval (In Failure) =
    return $ failureH
  eval (In (Bind m sc)) =
    do em <- eval (instantiate0 m)
       case em of
         In Failure -> return $ failureH
         In (Success m') -> eval (instantiate sc [instantiate0 m'])
         _ -> throwError $ "Cannot bind a non-computation: " ++ pretty em
  eval (In (Builtin n _)) =
    throwError $ "No builtin named " ++ n




evaluate :: Env (Sourced String) Term -> Term -> Either String Term
evaluate env m = runReaderT (eval m) env