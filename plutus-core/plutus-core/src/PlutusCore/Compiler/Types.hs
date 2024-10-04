{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns  #-}

module PlutusCore.Compiler.Types where

import Control.Monad.State.Class (MonadState)
import Control.Monad.State.Class qualified as State
import Data.Hashable
import PlutusCore.Builtin
import PlutusCore.Name.Unique
import PlutusCore.Quote
import UntypedPlutusCore.Core.Type qualified as UPLC

data UPLCSimplifierStage
  = FloatDelay
  | ForceDelay
  | CaseOfCase
  | CaseReduce
  | Inline
  | CSE

data UPLCSimplification name uni fun a =
  UPLCSimplification
    { beforeAST :: UPLC.Term name uni fun a
    , stage     :: UPLCSimplifierStage
    , afterAST  :: UPLC.Term name uni fun a
    }

-- TODO1: move somewhere more appropriate?
-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype UPLCSimplifierTrace name uni fun a =
  UPLCSimplifierTrace
    { uplcSimplifierTrace
      :: [UPLCSimplification name uni fun a]
    }

initUPLCSimplifierTrace :: UPLCSimplifierTrace name uni fun a
initUPLCSimplifierTrace = UPLCSimplifierTrace []

recordSimplification
  :: MonadState (UPLCSimplifierTrace name uni fun a) m
  => UPLC.Term name uni fun a
  -> UPLCSimplifierStage
  -> UPLC.Term name uni fun a
  -> m ()
recordSimplification beforeAST stage afterAST =
  let simplification = UPLCSimplification { beforeAST, stage, afterAST }
    in
      State.modify' $ \st ->
        st { uplcSimplifierTrace = uplcSimplifierTrace st ++ [simplification] }

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
