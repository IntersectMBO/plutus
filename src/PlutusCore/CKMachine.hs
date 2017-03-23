{-# OPTIONS -Wall #-}






module PlutusCore.CKMachine where

import PlutusCore.BuiltinEvaluation
import PlutusCore.PatternMatching
import PlutusCore.Term
import Utils.ABT
import Utils.Env
import Utils.Names
import Utils.Pretty







data CKFrame = InLet (Scope TermF)
             | InAppLeft Term
             | InAppRight Term
             | InCon String [Term] [Term]
             | InCase [Term] [Term] [ClauseF (Scope TermF)]
             | InSuccess
             | InBind (Scope TermF)
             | InBuiltin String [Term] [Term]

type CKStack = [CKFrame]





rec :: Int -> Env (Sourced String) Term -> CKStack -> Term -> Either String Term
rec 0 _ _ _ = Left "Out of petrol."
rec _ _ _ (Var x) =
  Right (Var x)
rec petrol denv stk (In (Decname n _)) =
  case lookup n denv of
    Nothing ->
      Left ("Unknown constant/defined term: " ++ showSourced n)
    Just m ->
      ret (petrol - 1) denv stk m
rec petrol denv stk (In (Let m sc)) =
  rec (petrol - 1) denv (InLet sc : stk) (instantiate0 m)
rec petrol denv stk m@(In (Lam _ _)) =
  ret (petrol - 1) denv stk m
rec petrol denv stk (In (App f x)) =
  rec (petrol - 1) denv (InAppLeft (instantiate0 x) : stk) (instantiate0 f)
rec petrol denv stk m@(In (Con _ [])) =
  ret (petrol - 1) denv stk m
rec petrol denv stk (In (Con c (m:ms))) =
  rec (petrol - 1) denv (InCon c [] (map instantiate0 ms) : stk) (instantiate0 m)
rec petrol denv stk (In (Case [] cs)) =
  case matchClauses cs [] of
    Nothing ->
      Left ("Incomplete pattern match: "
             ++ pretty (In (Case [] cs)))
    Just m'  ->
      rec (petrol - 1) denv stk m'
rec petrol denv stk (In (Case (m:ms) cs)) =
  rec (petrol - 1) denv (InCase [] (map instantiate0 ms) cs : stk) (instantiate0 m)
rec petrol denv stk (In (Success m)) =
  rec (petrol - 1) denv (InSuccess : stk) (instantiate0 m)
rec petrol denv stk m@(In (Failure _)) =
  ret (petrol - 1) denv stk m
rec petrol denv stk (In (Bind m sc)) =
  rec (petrol - 1) denv (InBind sc : stk) (instantiate0 m)
rec petrol denv stk m@(In (PrimData _)) =
  ret (petrol - 1) denv stk m
rec petrol denv stk (In (Builtin n [])) =
  case builtin n [] of
    Left err ->
      Left err
    Right m' ->
      ret (petrol - 1) denv stk m'
rec petrol denv stk (In (Builtin n (m:ms))) =
  rec (petrol - 1) denv (InBuiltin n [] (map instantiate0 ms) : stk) (instantiate0 m)





ret :: Int -> Env (Sourced String) Term -> CKStack -> Term -> Either String Term
ret 0 _ _ _ = Left "Out of petrol."
ret _ _ [] tm = Right tm
ret petrol denv (InLet sc : stk) m =
  rec (petrol - 1) denv stk (instantiate sc [m])
ret petrol denv (InAppLeft x : stk) f =
  rec (petrol - 1) denv (InAppRight f : stk) x
ret petrol denv (InAppRight f : stk) x =
  case f of
    In (Lam _ sc) ->
      rec (petrol - 1) denv stk (instantiate sc [x])
    _ ->
      ret (petrol - 1) denv stk (appH f x)
ret petrol denv (InCon c revls rs : stk) m =
  case rs of
    [] -> ret (petrol - 1) denv stk (conH c (reverse (m:revls)))
    m':rs' -> rec (petrol - 1) denv (InCon c (m:revls) rs' : stk) m'
ret petrol denv (InCase revls rs cs : stk) m =
  case rs of
    [] ->
      let ems = reverse (m:revls)
      in case matchClauses cs ems of
        Nothing ->
          Left ("Incomplete pattern match: "
                 ++ pretty (In (Case (map (scope []) ems) cs)))
        Just m'  ->
          rec (petrol - 1) denv stk m'
    m':rs' -> rec (petrol - 1) denv (InCase (m:revls) rs' cs : stk) m'
ret petrol denv (InSuccess : stk) m =
  ret (petrol - 1) denv stk (successH m)
ret petrol denv (InBind sc : stk) m =
  case m of
    In (Failure a) ->
      ret (petrol - 1) denv stk (failureH a)
    In (Success m') ->
      rec (petrol - 1) denv stk (instantiate sc [instantiate0 m'])
    _ ->
      Left ("Cannot bind a non-computation: " ++ pretty m)
ret petrol denv (InBuiltin n revls rs : stk) m =
  case rs of
    [] -> case builtin n (reverse (m:revls)) of
      Left err ->
        Left err
      Right m' ->
        ret (petrol - 1) denv stk m'
    m':rs' ->
      rec (petrol - 1) denv (InBuiltin n (m:revls) rs' : stk) m'




evaluate :: Env (Sourced String) Term -> Term -> Either String Term
evaluate denv tm = rec 3750 denv [] tm