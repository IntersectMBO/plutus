{-# OPTIONS -Wall #-}







module PlutusCore.PatternMatching where

import PlutusCore.Term
import Utils.ABT

import Control.Monad







matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (Var _) v = Just [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM matchPattern (map body ps) (map body as))
matchPattern (In (PrimPat x)) (In (PrimData y))
  | x == y = Just []
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