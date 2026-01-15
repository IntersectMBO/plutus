{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.CaseApply
    ( caseApply
    ) where

import Data.Vector qualified as V
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseApply), SimplifierT,
                                               recordSimplification)

caseApply
  :: Monad m
  => Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
caseApply term = do
  let result = processNestedApp term
  recordSimplification term CaseApply result
  return result

{- |
Transforms
@@
[[[[f a] b] c] ...]
@@
Into
@@
(case (constr 0 a b c ...) f)
@@
-}
processNestedApp
  :: Term name uni fun a
  -> Term name uni fun a
processNestedApp (Apply ann body arg) =
  -- Any nested application with fewer than 3 nested application is cheaper to represent
  -- using a regular 'Apply' node. This is because the CaseApply optimization introduces
  -- two AST nodes—'Constr' and 'Case'. Transforming a single application or a two-nested
  -- application into 'Constr' and 'Case' actually hurts performance.
  -- See #7410 for more information.
  if length args >= 3
  then
    Case ann
      (Constr ann 0 (processNestedApp <$> args))
      (V.singleton (processNestedApp innerBody))
  else Apply ann (processNestedApp body) (processNestedApp arg)
  where
    (args, innerBody) = consumeApp [arg] body
    consumeApp as (Apply _ body' arg') = consumeApp (arg':as) body'
    consumeApp as t                    = (as, t)
processNestedApp (LamAbs ann name t) =
  LamAbs ann name (processNestedApp  t)
processNestedApp (Force ann t) =
  Force ann (processNestedApp t)
processNestedApp (Delay ann t) =
  Delay ann (processNestedApp t)
processNestedApp (Constr ann idx ts) =
  Constr ann idx (processNestedApp <$> ts)
processNestedApp (Case ann t bs) =
  Case ann (processNestedApp t) (processNestedApp <$> bs)
processNestedApp (Var ann n) = Var ann n
processNestedApp (Constant ann v) = Constant ann v
processNestedApp (Builtin ann fun) = Builtin ann fun
processNestedApp (Error ann) = Error ann
