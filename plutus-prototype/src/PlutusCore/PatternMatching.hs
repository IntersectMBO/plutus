{-# OPTIONS -Wall #-}







module PlutusCore.PatternMatching where

import           PlutusCore.Term
import           Utils.ABT

import           Control.Monad







matchPattern :: SimplePattern -> Int -> Term -> Maybe [Term]
matchPattern (VarPat _) _ v =
  Just [v]
matchPattern (ConPat c) l (In (Con c' as))
  | c == c' && l == length as =
    Just (map instantiate0 as)
matchPattern _ _ _ = Nothing

matchClauses :: [Clause] -> Term -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause c sc:cs) v =
  case matchPattern c (length (names sc)) v of
    Nothing -> matchClauses cs v
    Just xs -> Just (instantiate sc xs)
