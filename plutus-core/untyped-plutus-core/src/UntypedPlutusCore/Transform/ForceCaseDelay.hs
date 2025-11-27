{-# LANGUAGE LambdaCase #-}

{- Note [Applying force to delays in case branches]

Often, the following pattern occurs in UPLC terms:

> force (case scrut [\x1... -> delay term_1, ..., \x1... -> delay term_m])

It's sound to remove the 'force' and the 'delay's, as long as the original term is "well-formed".
Note that the lambda abstraction may be missing, and we consider that case as well.

Intuitively, what we mean by "well-formed" is that the term does not evaluate to bottom unless
the user intended it to (i.e. by introducing an 'error' subterm).

In the the context of the Plinth compiler pipeline, UPLC is always generated from TPLC, by
erasing the types of a TPLC term. So at the beginning of the UPLC phase of the compiler,
the UPLC can be considered "well-formed", since it is guaranteed by the types of the original
TPLC term.

The other UPLC transformations we have are guaranteed to preserve this property, so we can assume
that any UPLC term coming from the UPLC phase of the compiler is "well-formed".

What about preserving the correct evaluation strategy? Since we are removing 'delay's, we need to
ensure that the terms under the delays are not evaluated ahead of time. However, this is not a problem
because the 'case' construct is lazy in its branches, so the terms under the 'delay's will not be
evaluated unless the corresponding branch is taken.

We should, however, formally define what "well-formed" means, and this is left as future work:
FIXME(https://github.com/IntersectMBO/plutus-private/issues/1644).

-}
module UntypedPlutusCore.Transform.ForceCaseDelay
  ( forceCaseDelay
  )
where

import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier
  ( SimplifierStage (ForceCaseDelay)
  , SimplifierT
  , recordSimplification
  )

import Control.Lens

forceCaseDelay
  :: Monad m
  => Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
forceCaseDelay term = do
  let result = transformOf termSubterms processTerm term
  recordSimplification term ForceCaseDelay result
  return result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
  original@(Force _ (Case cAnn scrut branches)) ->
    let mNewBranches = traverse findDelayUnderLambdas branches
     in case mNewBranches of
          Just newBranches ->
            Case cAnn scrut newBranches
          Nothing -> original
  other -> other
  where
    findDelayUnderLambdas :: Term name uni fun a -> Maybe (Term name uni fun a)
    findDelayUnderLambdas = \case
      LamAbs ann var body -> LamAbs ann var <$> findDelayUnderLambdas body
      Delay _ term -> Just term
      _ -> Nothing
