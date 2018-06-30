{-# OPTIONS -Wall #-}






module PlutusCore.CKMachine where

import PlutusCore.BuiltinEvaluation
import PlutusCore.EvaluatorTypes
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
             | InCase [ClauseF (Scope TermF)]
             | InSuccess
             | InBind (Scope TermF)
             | InBuiltin String [Term] [Term]

type CKStack = [CKFrame]





rec :: Petrol -> TransactionInfo -> SourcedEnv -> CKStack -> Term -> Either String Term
rec 0 _ _ _ _ = Left "Out of petrol."
rec _ _ _ _ (Var x) =
  Right (Var x)
rec petrol txinfo denv stk (In (Decname n)) =
  case lookup n denv of
    Nothing ->
      Left ("Unknown constant/defined term: " ++ showSourced n)
    Just m ->
      ret (petrol - 1) txinfo denv stk m
rec petrol txinfo denv stk (In (Let m sc)) =
  rec (petrol - 1) txinfo denv (InLet sc : stk) (instantiate0 m)
rec petrol txinfo denv stk m@(In (Lam _)) =
  ret (petrol - 1) txinfo denv stk m
rec petrol txinfo denv stk (In (App f x)) =
  rec (petrol - 1) txinfo denv (InAppLeft (instantiate0 x) : stk) (instantiate0 f)
rec petrol txinfo denv stk m@(In (Con _ [])) =
  ret (petrol - 1) txinfo denv stk m
rec petrol txinfo denv stk (In (Con c (m:ms))) =
  rec (petrol - 1) txinfo denv (InCon c [] (map instantiate0 ms) : stk) (instantiate0 m)
rec petrol txinfo denv stk (In (Case m cs)) =
  rec (petrol - 1) txinfo denv (InCase cs : stk) (instantiate0 m)
rec petrol txinfo denv stk (In (Success m)) =
  rec (petrol - 1) txinfo denv (InSuccess : stk) (instantiate0 m)
rec petrol txinfo denv stk m@(In Failure) =
  ret (petrol - 1) txinfo denv stk m
rec petrol txinfo denv stk (In (Bind m sc)) =
  rec (petrol - 1) txinfo denv (InBind sc : stk) (instantiate0 m)
rec petrol txinfo denv stk (In TxHash) =
  ret (petrol - 1) txinfo denv stk (primByteStringH (txHash txinfo))
rec petrol txinfo denv stk (In TxDistrHash) =
  ret (petrol - 1) txinfo denv stk (primByteStringH (txDistrHash txinfo))
rec petrol txinfo denv stk m@(In (PrimData _)) =
  ret (petrol - 1) txinfo denv stk m
rec petrol txinfo denv stk (In (Builtin n [])) =
  case builtin n [] of
    Left err ->
      Left err
    Right m' ->
      ret (petrol - 1) txinfo denv stk m'
rec petrol txinfo denv stk (In (Builtin n (m:ms))) =
  rec (petrol - 1) txinfo denv (InBuiltin n [] (map instantiate0 ms) : stk) (instantiate0 m)





ret :: Petrol -> TransactionInfo -> SourcedEnv -> CKStack -> Term -> Either String Term
ret 0 _ _ _ _ = Left "Out of petrol."
ret _ _ _ [] tm = Right tm
ret petrol txinfo denv (InLet sc : stk) m =
  rec (petrol - 1) txinfo denv stk (instantiate sc [m])
ret petrol txinfo denv (InAppLeft x : stk) f =
  rec (petrol - 1) txinfo denv (InAppRight f : stk) x
ret petrol txinfo denv (InAppRight f : stk) x =
  case f of
    In (Lam sc) ->
      rec (petrol - 1) txinfo denv stk (instantiate sc [x])
    _ ->
      ret (petrol - 1) txinfo denv stk (appH f x)
ret petrol txinfo denv (InCon c revls rs : stk) m =
  case rs of
    [] -> ret (petrol - 1) txinfo denv stk (conH c (reverse (m:revls)))
    m':rs' -> rec (petrol - 1) txinfo denv (InCon c (m:revls) rs' : stk) m'
ret petrol txinfo denv (InCase cs : stk) m =
  case matchClauses cs m of
    Nothing ->
      Left ("Incomplete pattern match: "
             ++ pretty (In (Case (scope [] m) cs)))
    Just m'  ->
      rec (petrol - 1) txinfo denv stk m'
ret petrol txinfo denv (InSuccess : stk) m =
  ret (petrol - 1) txinfo denv stk (successH m)
ret petrol txinfo denv (InBind sc : stk) m =
  case m of
    In Failure ->
      ret (petrol - 1) txinfo denv stk failureH
    In (Success m') ->
      rec (petrol - 1) txinfo denv stk (instantiate sc [instantiate0 m'])
    _ ->
      Left ("Cannot bind a non-computation: " ++ pretty m)
ret petrol txinfo denv (InBuiltin n revls rs : stk) m =
  case rs of
    [] -> case builtin n (reverse (m:revls)) of
      Left err ->
        Left err
      Right m' ->
        ret (petrol - 1) txinfo denv stk m'
    m':rs' ->
      rec (petrol - 1) txinfo denv (InBuiltin n (m:revls) rs' : stk) m'




evaluate :: TransactionInfo -> SourcedEnv -> Petrol -> Term -> Either String Term
evaluate txinfo denv ptrl tm = rec ptrl txinfo denv [] tm