{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeFamilies   #-}

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

{-# LANGUAGE StrictData     #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Evaluation.Machine.Exception

import Control.DeepSeq
import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import PlutusCore.Builtin.KnownType

import PlutusCore.Builtin.Emitter
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory

data Nat = Z | S Nat

-- | Same as 'TypeScheme' except this one doesn't contain any evaluation-irrelevant types stuff.
data BuiltinRuntime val
    = BuiltinRuntimeResult {-# UNPACK #-} ExBudget ~(MakeKnownM val)
    | BuiltinRuntimeArrow (ExMemory -> val -> BuiltinRuntime val)
    | BuiltinRuntimeAll (BuiltinRuntime val)

type MakeKnownM = ExceptT (ErrorWithCause ReadKnownError ()) Emitter
type ReadKnownM = Either (ErrorWithCause ReadKnownError ())

instance NFData (BuiltinRuntime val) where
    rnf = error "fix me somehow" -- (BuiltinRuntime rs f exF) = rnf rs `seq` f `seq` rwhnf exF

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

deriving newtype instance (NFData fun) => NFData (BuiltinsRuntime fun val)

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
