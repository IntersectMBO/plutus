{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

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

import Data.DList qualified as DList
import Data.Typeable (Proxy (..))
import PlutusCore.Arity (Param (..), builtinArity)
import PlutusCore.Builtin.Meaning (ToBuiltinMeaning (..))
import PlutusCore.Pretty (Pretty (pretty), PrettyBy (prettyBy))
import Prettyprinter (vsep, (<+>))
import UntypedPlutusCore.Core (Term (..))

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

{- | Either the "next" term to be evaluated, along with its 'Purity' and 'WorkFreedom',
or we don't know what comes next.
-}
data EvalTerm name uni fun a
  = Unknown
  | EvalTerm Purity WorkFreedom (Term name uni fun a)

instance
  (PrettyBy config (Term name uni fun a))
  => PrettyBy config (EvalTerm name uni fun a)
  where
  prettyBy _ Unknown                    = "<unknown>"
  prettyBy config (EvalTerm eff work t) = pretty eff <+> pretty work <> ":" <+> prettyBy config t

-- We use a DList here for efficient and lazy concatenation

-- | The order in which terms get evaluated, along with their purities.
newtype EvalOrder name uni fun a = EvalOrder (DList.DList (EvalTerm name uni fun a))
  deriving newtype (Semigroup, Monoid)

{- | Get the evaluation order as a list of 'EvalTerm's. Either terminates in a single
'Unknown', which means that we got to a point where evaluation continues but we don't
know where; or terminates normally, in which case we actually got to the end of the
evaluation order for the term.
-}
unEvalOrder :: EvalOrder name uni fun a -> [EvalTerm name uni fun a]
unEvalOrder (EvalOrder ts) =
  -- This is where we avoid traversing the whole program beyond the first Unknown,
  -- since DList is lazy and we convert to a lazy list and then filter it.
  takeWhileInclusive (\case Unknown -> False; _ -> True) (DList.toList ts)
 where
  takeWhileInclusive :: (a -> Bool) -> [a] -> [a]
  takeWhileInclusive p = foldr (\x ys -> if p x then x : ys else [x]) []

singletonEvalOrder :: EvalTerm name uni fun a -> EvalOrder name uni fun a
singletonEvalOrder = EvalOrder . DList.singleton

instance (PrettyBy config (Term name uni fun a)) => PrettyBy config (EvalOrder name uni fun a) where
  prettyBy config eo = vsep $ fmap (prettyBy config) (unEvalOrder eo)

-- Terms can have Type and Term parameters.
-- In correct programs Type parameters are 'Force'd while
-- term parameters are 'Apply'd.
-- This data type represents this distinction.
data Arg name uni fun a = ApplyTerm (Term name uni fun a) | ForceTypeParam

-- | Strip off arguments
splitArgs :: Term name uni fun a -> (Term name uni fun a, [Arg name uni fun a])
splitArgs = go []
  where
  go arguments = \case
    Apply _ann function argument -> go (ApplyTerm argument : arguments) function
    Force _ann forcedTerm -> go (ForceTypeParam : arguments) forcedTerm
    term -> (term, arguments)

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
   . (ToBuiltinMeaning uni fun)
  => BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> EvalOrder name uni fun a
termEvaluationOrder builtinSemanticsVariant = goTerm
 where
  goTerm :: Term name uni fun a -> EvalOrder name uni fun a
  goTerm = \case
    t@(splitArgs -> (Builtin _ann fun, args)) ->
      foldMap goTerm [ a | ApplyTerm a <- args ] <> termEvalOrder parameters args
     where
      parameters :: [Param] =
        builtinArity @uni @fun (Proxy @uni) builtinSemanticsVariant fun

      termEvalOrder :: [Param] -> [Arg name uni fun a] -> EvalOrder name uni fun a
      termEvalOrder [] _ =
        singletonEvalOrder (EvalTerm MaybeImpure MaybeWork t)
      -- Builtin is not fully saturated with term arguments, thus impure.
      termEvalOrder (TermParam : _params) [] =
        singletonEvalOrder (EvalTerm Pure WorkFree t)
      -- Strip applied term parameter
      termEvalOrder (TermParam : params) (_arg : remainingArgs) =
        termEvalOrder params remainingArgs
      -- Strip applied type parameter
      termEvalOrder (TypeParam : params) (ForceTypeParam : remainingArgs) =
        termEvalOrder params remainingArgs
      -- Type parameter expected, non-Force argument applied. Error is impure.
      termEvalOrder (TypeParam : _remainingParams) _ =
        singletonEvalOrder (EvalTerm MaybeImpure MaybeWork t)

    t@(Apply _ fun arg) ->
      -- first the function
      goTerm fun
        -- then the arg
        <> goTerm arg
        -- then the whole term, which means environment manipulation, so work
        <> singletonEvalOrder (EvalTerm Pure MaybeWork t)
        <> case fun of
          -- known function body
          LamAbs _ _ body -> goTerm body
          -- unknown function body
          _               -> singletonEvalOrder Unknown
    t@(Force _ dterm) ->
      -- first delayed term
      goTerm dterm
        -- then the whole term, which will mean forcing, so work
        <> singletonEvalOrder (EvalTerm Pure MaybeWork t)
        <> case dterm of
          -- known delayed term
          Delay _ body -> goTerm body
          -- unknown delayed term
          _            -> singletonEvalOrder Unknown
    t@(Constr _ _ ts) ->
      -- first the arguments, in left-to-right order
      foldMap goTerm ts
        -- then the whole term, which means constructing the value, so work
        <> singletonEvalOrder (EvalTerm Pure MaybeWork t)
    t@(Case _ scrut _) ->
      -- first the scrutinee
      goTerm scrut
        -- then the whole term, which means finding the case so work
        <> singletonEvalOrder (EvalTerm Pure MaybeWork t)
        -- then we go to an unknown scrutinee
        <> singletonEvalOrder Unknown
    -- Leaf terms
    t@Var{} ->
      singletonEvalOrder (EvalTerm Pure WorkFree t)
    t@Error{} ->
      -- definitely effectful! but not relevant from a work perspective
      singletonEvalOrder (EvalTerm MaybeImpure WorkFree t)
        -- program terminates
        <> singletonEvalOrder Unknown
    t@Builtin{} ->
      singletonEvalOrder (EvalTerm Pure WorkFree t)
    t@Delay{} ->
      singletonEvalOrder (EvalTerm Pure WorkFree t)
    t@LamAbs{} ->
      singletonEvalOrder (EvalTerm Pure WorkFree t)
    t@Constant{} ->
      singletonEvalOrder (EvalTerm Pure WorkFree t)

{- | Will evaluating this term have side effects (looping or error)?
This is slightly wider than the definition of a value, as
it includes applications that are known to be pure, as well as
things that can't be returned from the machine (as they'd be ill-scoped).
-}
isPure
  :: (ToBuiltinMeaning uni fun)
  => BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> Bool
isPure builtinSemanticsVariant term =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go (unEvalOrder (termEvaluationOrder builtinSemanticsVariant term))
 where
  go :: [EvalTerm name uni fun a] -> Bool
  go [] = True
  go (et : rest) = case et of
    -- Might be an effect here!
    EvalTerm MaybeImpure _ _ -> False
    -- This term is fine, what about the rest?
    EvalTerm Pure _ _        -> go rest
    -- We don't know what will happen, so be conservative
    Unknown                  -> False

{- | Is the given term 'work-free'?

Note: The definition of 'work-free' is a little unclear, but the idea is that
evaluating this term should do very a trivial amount of work.
-}
isWorkFree
  :: (ToBuiltinMeaning uni fun)
  => BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> Bool
isWorkFree builtinSemanticsVariant term =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go (unEvalOrder (termEvaluationOrder builtinSemanticsVariant term))
 where
  go :: [EvalTerm name uni fun a] -> Bool
  go [] = True
  go (et : rest) = case et of
    -- Might be an effect here!
    EvalTerm _ MaybeWork _ -> False
    -- This term is fine, what about the rest?
    EvalTerm _ WorkFree _  -> go rest
    -- We don't know what will happen, so be conservative
    Unknown                -> False
