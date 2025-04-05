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
  , WorkFreedom (..)
  , termEvaluationOrder
  ) where

import Data.DList qualified as DList
import Data.Typeable (Proxy (..))
import PlutusCore.Arity (Param (..), builtinArity)
import PlutusCore.Builtin.Meaning (ToBuiltinMeaning (..))
import PlutusCore.Pretty (Pretty (pretty), PrettyBy (prettyBy))
import Prettyprinter (vsep, (<+>))
import Universe.Core (Closed, Everywhere, GShow)
import UntypedPlutusCore.Contexts (AppCtx (..), fillAppCtx, splitAppCtx)
import UntypedPlutusCore.Core (Term (..))
import UntypedPlutusCore.Core.Instance.Eq ()

-- | Is this pure? Either yes, or maybe not.
data Purity = MaybeImpure | Pure
  deriving stock (Eq, Show)

instance Pretty Purity where
  pretty MaybeImpure = "impure?"
  pretty Pure        = "pure"

-- | Is this term essentially work-free? Either yes, or maybe not.
data WorkFreedom = MaybeWork | WorkFree
  deriving stock (Eq, Show)

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
 ( Show name
 , Everywhere uni Show
 , Show fun
 , Show a
 , GShow uni
 , Closed uni
 ) => Show (EvalTerm name uni fun a) where
  show = \case
    Unknown -> "<unknown>"
    EvalTerm purity work t ->
      "EvalTerm " <> show purity <> " " <> show work <> " " <> show t

instance (PrettyBy config (Term name uni fun a))
  => PrettyBy config (EvalTerm name uni fun a) where
  prettyBy _ Unknown = "<unknown>"
  prettyBy config (EvalTerm eff work t) =
    pretty eff <+> pretty work <> ":" <+> prettyBy config t

instance Eq (Term name uni fun a) => Eq (EvalTerm name uni fun a) where
  Unknown == Unknown                         = True
  (EvalTerm p1 w1 t1) == (EvalTerm p2 w2 t2) = p1 == p2 && w1 == w2 && t1 == t2
  _ == _                                     = False

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

eval :: EvalTerm name uni fun a -> EvalOrder name uni fun a
eval = EvalOrder . DList.singleton

instance (PrettyBy config (Term name uni fun a)) =>
  PrettyBy config (EvalOrder name uni fun a) where
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
   . (ToBuiltinMeaning uni fun)
  => BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> EvalOrder name uni fun a
termEvaluationOrder builtinSemanticsVariant = goTerm
 where
  goTerm :: Term name uni fun a -> EvalOrder name uni fun a
  goTerm = \case
    (splitAppCtx -> (builtin@(Builtin _ann fun), appCtx)) ->
      appCtxEvalOrder appCtx <> go arity appCtx
     where
      arity = builtinArity @uni @fun (Proxy @uni) builtinSemanticsVariant fun

      appCtxEvalOrder :: AppCtx name uni fun a -> EvalOrder name uni fun a
      appCtxEvalOrder = \case
        AppCtxEnd -> mempty
        AppCtxTerm _ t rest -> goTerm t <> appCtxEvalOrder rest
        AppCtxType _ rest -> appCtxEvalOrder rest

      go :: [Param] -> AppCtx name uni fun a -> EvalOrder name uni fun a
      go parameters appContext =
        case parameters of
          -- All builtin parameters have been applied,
          -- (such term is considered impure).
          [] -> maybeImpureWork

          -- A term parameter is waiting to be applied
          TermParam : otherParams ->
            case appContext of
              AppCtxEnd ->
                -- Builtin is not fully saturated with term arguments, thus pure.
                pureWorkFree
              AppCtxType _ann _remainingAppCtx ->
                -- Term parameter expected, type argument applied.
                -- Error is impure.
                maybeImpureWork
              AppCtxTerm _ann _argTerm remainingAppCtx ->
                go otherParams remainingAppCtx

          -- A type parameter is waiting to be forced
          TypeParam : otherParams ->
            case appContext of
              AppCtxEnd ->
                -- Builtin is not fully saturated with type arguments, thus pure.
                pureWorkFree
              AppCtxTerm _ann _term _remainingAppCtx ->
                -- Type parameter expected, term argument applied.
                -- Error is impure.
                maybeImpureWork
              AppCtxType _ann remainingAppCtx ->
                go otherParams remainingAppCtx

        where
        maybeImpureWork :: EvalOrder name uni fun a
        maybeImpureWork = eval (EvalTerm MaybeImpure MaybeWork reconstructed)

        pureWorkFree :: EvalOrder name uni fun a
        pureWorkFree = eval (EvalTerm Pure WorkFree reconstructed)

        reconstructed :: Term name uni fun a
        reconstructed = fillAppCtx builtin appCtx

    t@(Apply _ fun arg) ->
      -- first the function
      goTerm fun
        -- then the arg
        <> goTerm arg
        -- then the whole term, which means environment manipulation, so work
        <> eval (EvalTerm Pure MaybeWork t)
        <> case fun of
          -- known function body
          LamAbs _ _ body -> goTerm body
          -- unknown function body
          _               -> eval Unknown
    t@(Force _ dterm) ->
      -- first delayed term
      goTerm dterm
        -- then the whole term, which will mean forcing, so work
        <> eval (EvalTerm Pure MaybeWork t)
        <> case dterm of
          -- known delayed term
          Delay _ body -> goTerm body
          -- unknown delayed term
          _            -> eval Unknown
    t@(Constr _ _ ts) ->
      -- first the arguments, in left-to-right order
      foldMap goTerm ts
        -- then the whole term, which means constructing the value, so work
        <> eval (EvalTerm Pure MaybeWork t)
    t@(Case _ scrut _) ->
      -- first the scrutinee
      goTerm scrut
        -- then the whole term, which means finding the case so work
        <> eval (EvalTerm Pure MaybeWork t)
        -- then we go to an unknown scrutinee
        <> eval Unknown
    -- Leaf terms
    t@Var{} ->
      eval (EvalTerm Pure WorkFree t)
    t@Error{} ->
      -- definitely effectful! but not relevant from a work perspective
      eval (EvalTerm MaybeImpure WorkFree t)
        -- program terminates
        <> eval Unknown
    t@Builtin{} ->
      eval (EvalTerm Pure WorkFree t)
    t@Delay{} ->
      eval (EvalTerm Pure WorkFree t)
    t@LamAbs{} ->
      eval (EvalTerm Pure WorkFree t)
    t@Constant{} ->
      eval (EvalTerm Pure WorkFree t)

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
