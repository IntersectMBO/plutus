{-# LANGUAGE NamedFieldPuns #-}

module UntypedPlutusCore.Transform.Simplifier (
    Simplifier,
    SimplifierTrace (..),
    SimplifierStage (..),
    Simplification (..),
    initSimplifierTrace,
    recordSimplification,
) where

import Control.Monad.State (StateT)
import Control.Monad.State qualified as State
import UntypedPlutusCore.Core.Type (Term)

type Simplifier name uni fun a m = StateT (SimplifierTrace name uni fun a) m

data SimplifierStage
  = FloatDelay
  | ForceDelay
  | CaseOfCase
  | CaseReduce
  | Inline
  | CSE

data Simplification name uni fun a =
  Simplification
    { beforeAST :: Term name uni fun a
    , stage     :: SimplifierStage
    , afterAST  :: Term name uni fun a
    }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype SimplifierTrace name uni fun a =
  SimplifierTrace
    { simplifierTrace
      :: [Simplification name uni fun a]
    }

initSimplifierTrace :: SimplifierTrace name uni fun a
initSimplifierTrace = SimplifierTrace []

recordSimplification
  :: Monad m
  => Term name uni fun a
  -> SimplifierStage
  -> Term name uni fun a
  -> Simplifier name uni fun a m ()
recordSimplification beforeAST stage afterAST =
  let simplification = Simplification { beforeAST, stage, afterAST }
    in
      State.modify' $ \st ->
        st { simplifierTrace = simplifierTrace st ++ [simplification] }
