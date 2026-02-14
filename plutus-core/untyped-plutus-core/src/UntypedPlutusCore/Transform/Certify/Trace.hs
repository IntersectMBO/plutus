module UntypedPlutusCore.Transform.Certify.Trace where

import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify

data SimplifierStage
  = FloatDelay
  | ForceDelay
  | ForceCaseDelay
  | CaseOfCase
  | CaseReduce
  | Inline
  | CSE
  deriving stock (Show)

data Simplification name uni fun a
  = Simplification
  { beforeAST :: Term name uni fun a
  , stage :: SimplifierStage
  , hints :: Certify.Hints
  , afterAST :: Term name uni fun a
  }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype SimplifierTrace name uni fun a
  = SimplifierTrace
  { simplifierTrace
      :: [Simplification name uni fun a]
  }

initSimplifierTrace :: SimplifierTrace name uni fun a
initSimplifierTrace = SimplifierTrace []
