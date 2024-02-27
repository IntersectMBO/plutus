{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.ForceApply
    ( forceApply
    ) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)
import Control.Monad (guard)
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)

forceApply :: Term name uni fun a -> Term name uni fun a
forceApply = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    original@(Force _ subTerm) ->
        fromMaybe original (optimisationProcedure subTerm)
    t -> t

-- TODO: use NonEmpty
data MultiApply name uni fun a = MultiApply
    { toApply     :: Term name uni fun a
    , applyToIter :: [(a, Term name uni fun a)]
    }

toMultiApply :: Term name uni fun a -> Maybe (MultiApply name uni fun a)
toMultiApply term =
    case term of
        Apply _ _ _ -> run [] term
        _           -> Nothing
  where
    run acc (Apply a t1 t2) =
        run ((a, t2) : acc) t1
    run acc t =
        pure $ MultiApply t acc

fromMultiApply :: MultiApply name uni fun a -> Term name uni fun a
fromMultiApply (MultiApply term ts) =
    foldl' (\acc (ann, arg) -> Apply ann acc arg) term ts

data MultiAbs name uni fun a = MultiAbs
    { absVars :: [(a, name)]
    , rhs     :: Term name uni fun a
    }

toMultiAbs :: Term name uni fun a -> Maybe (MultiAbs name uni fun a)
toMultiAbs term =
    case term of
        LamAbs _ _ _ -> run [] term
        _            -> Nothing
  where
    run acc (LamAbs a name t) =
        run ((a, name) : acc) t
    run acc t =
        pure $ MultiAbs acc t

fromMultiAbs :: MultiAbs name uni fun a -> Term name uni fun a
fromMultiAbs (MultiAbs vars term) =
    foldl' (\acc (ann, name) -> LamAbs ann name acc) term vars

optimisationProcedure :: Term name uni fun a -> Maybe (Term name uni fun a)
optimisationProcedure term = do
    asMultiApply <- toMultiApply term
    innerMultiAbs <- toMultiAbs . toApply $ asMultiApply
    guard $ length (applyToIter asMultiApply) == length (absVars innerMultiAbs)
    case rhs innerMultiAbs of
        Delay _ subTerm ->
            let optimisedInnerMultiAbs = innerMultiAbs { rhs = subTerm}
                optimisedMultiApply =
                    asMultiApply { toApply = fromMultiAbs optimisedInnerMultiAbs }
            in pure . fromMultiApply $ optimisedMultiApply
        _               -> Nothing



