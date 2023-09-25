{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
-- Stripped-down version of PlutusIR.Purity
module UntypedPlutusCore.Purity
    ( isPure
    , isWorkFree
    , EvalOrder
    , unEvalOrder
    , EvalTerm (..)
    , Purity (..)
    , termEvaluationOrder
    ) where

import PlutusCore.Pretty
import UntypedPlutusCore.Core.Type

import Data.DList qualified as DList
import Prettyprinter

-- | Is this pure? Either yes, or maybe not.
data Purity = MaybeImpure | Pure

instance Pretty Purity where
  pretty MaybeImpure = "impure?"
  pretty Pure        = "pure"

-- | Is this term essentially work-free? Either yes, or maybe not.
data WorkFreedom = MaybeWork | WorkFree

instance Pretty WorkFreedom where
  pretty MaybeWork = "maybe work?"
  pretty WorkFree  = "work-free"

-- | Either the "next" term to be evaluated, along with its 'Purity' and 'WorkFreedom',
-- or we don't know what comes next.
data EvalTerm name uni fun a =
  Unknown
  | EvalTerm Purity WorkFreedom (Term name uni fun a)

instance PrettyBy config (Term name uni fun a)
  => PrettyBy config (EvalTerm name uni fun a) where
  prettyBy _ Unknown                    = "<unknown>"
  prettyBy config (EvalTerm eff work t) = pretty eff <+> pretty work <> ":" <+> prettyBy config t

-- We use a DList here for efficient and lazy concatenation
-- | The order in which terms get evaluated, along with their purities.
newtype EvalOrder name uni fun a = EvalOrder (DList.DList (EvalTerm name uni fun a))
  deriving newtype (Semigroup, Monoid)

-- | Get the evaluation order as a list of 'EvalTerm's. Either terminates in a single
-- 'Unknown', which means that we got to a point where evaluation continues but we don't
-- know where; or terminates normally, in which case we actually got to the end of the
-- evaluation order for the term.
unEvalOrder :: EvalOrder name uni fun a -> [EvalTerm name uni fun a]
unEvalOrder (EvalOrder ts) =
  -- This is where we avoid traversing the whole program beyond the first Unknown,
  -- since DList is lazy and we convert to a lazy list and then filter it.
  takeWhileInclusive (\case { Unknown -> False; _ -> True })
  $ DList.toList ts
  where
    takeWhileInclusive :: (a -> Bool) -> [a] -> [a]
    takeWhileInclusive p = foldr (\x ys -> if p x then x:ys else [x]) []

evalThis :: EvalTerm name uni fun a -> EvalOrder name uni fun a
evalThis tm = EvalOrder (DList.singleton tm)

instance PrettyBy config (Term name uni fun a)
  => PrettyBy config (EvalOrder name uni fun a) where
  prettyBy config eo = vsep $ fmap (prettyBy config) (unEvalOrder eo)

{- | Given a term, return the order in which it and its sub-terms will be evaluated.

This aims to be a sound under-approximation: if we don't know, we just say 'Unknown'.
Typically there will be a sequence of terms that we do know, which will terminate
in 'Unknown' once we do something like call a function.

This makes some assumptions about the evaluator, in particular about the order in
which we evaluate sub-terms, but these match the current evaluator and we are not
planning on changing it.
-}
termEvaluationOrder
  :: forall name uni fun a
  . Term name uni fun a
  -> EvalOrder name uni fun a
termEvaluationOrder = goTerm
    where
      goTerm :: Term name uni fun a -> EvalOrder name uni fun a
      goTerm = \case
        t@(Apply _ fun arg)    ->
          -- first the function
          goTerm fun
          -- then the arg
          <> goTerm arg
          -- then the whole term, which means environment manipulation, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          <> dest
          where
            dest = case fun of
              -- known function body
              (LamAbs _ _ body) -> goTerm body
              -- unknown function body
              _                 -> evalThis Unknown
        t@(Force _ dterm)        ->
          -- first delayed term
          goTerm dterm
          -- then the whole term, which will mean forcing, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          <> dest
          where
            dest = case dterm of
              -- known delayed term
              (Delay _ body) -> goTerm body
              -- unknown delayed term
              _              -> evalThis Unknown

        t@(Constr _ _ ts)     ->
          -- first the arguments, in left-to-right order
          foldMap goTerm ts
          -- then the whole term, which means constructing the value, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
        t@(Case _ scrut _)    ->
          -- first the scrutinee
          goTerm scrut
          -- then the whole term, which means finding the case so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          -- then we go to an unknown scrutinee
          <> evalThis Unknown

        -- Leaf terms
        t@Var{} -> evalThis (EvalTerm Pure WorkFree t)
        t@Error{}           ->
          -- definitely effectful! but not relevant from a work perspective
          evalThis (EvalTerm MaybeImpure WorkFree t)
          -- program terminates
          <> evalThis Unknown
        t@Builtin{}         ->
          evalThis (EvalTerm Pure WorkFree t)
        t@Delay{}           ->
          evalThis (EvalTerm Pure WorkFree t)
        t@LamAbs{}          ->
          evalThis (EvalTerm Pure WorkFree t)
        t@Constant{}        ->
          evalThis (EvalTerm Pure WorkFree t)

-- | Will evaluating this term have side effects (looping or error)?
-- This is slightly wider than the definition of a value, as
-- it includes applications that are known to be pure, as well as
-- things that can't be returned from the machine (as they'd be ill-scoped).
isPure ::
    Term name uni fun a ->
    Bool
isPure t =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go $ unEvalOrder (termEvaluationOrder t)
  where
    go :: [EvalTerm name uni fun a] -> Bool
    go [] = True
    go (et:rest) = case et of
      -- Might be an effect here!
      EvalTerm MaybeImpure _ _ -> False
      -- This term is fine, what about the rest?
      EvalTerm Pure _ _        -> go rest
      -- We don't know what will happen, so be conservative
      Unknown                  -> False

{-| Is the given term 'work-free'?

Note: The definition of 'work-free' is a little unclear, but the idea is that
evaluating this term should do very a trivial amount of work.
-}
isWorkFree ::
    Term name uni fun a ->
    Bool
isWorkFree t =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go $ unEvalOrder (termEvaluationOrder t)
  where
    go :: [EvalTerm name uni fun a] -> Bool
    go [] = True
    go (et:rest) = case et of
      -- Might be an effect here!
      EvalTerm _ MaybeWork _ -> False
      -- This term is fine, what about the rest?
      EvalTerm _ WorkFree _  -> go rest
      -- We don't know what will happen, so be conservative
      Unknown                -> False
