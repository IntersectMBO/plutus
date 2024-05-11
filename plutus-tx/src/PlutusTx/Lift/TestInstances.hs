{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE UndecidableSuperClasses  #-}

module PlutusTx.Lift.TestInstances () where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusTx.Builtins.IsBuiltin
import PlutusTx.Lift.Class

import Data.Kind qualified as GHC

type BuiltinSatisfies
    :: (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Constraint)
    -> GHC.Type
    -> GHC.Constraint
class    (pre (ToBuiltin a) => post (ToBuiltin a)) => BuiltinSatisfies pre post a
instance (pre (ToBuiltin a) => post (ToBuiltin a)) => BuiltinSatisfies pre post a

type AllBuiltinsSatisfy
    :: (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Constraint)
    -> GHC.Constraint
class PLC.DefaultUni `PLC.Everywhere` BuiltinSatisfies pre post => AllBuiltinsSatisfy pre post

instance AllBuiltinsSatisfy
    (PLC.AllBuiltinArgs PLC.DefaultUni (Typeable PLC.DefaultUni))
    (Typeable PLC.DefaultUni)
instance AllBuiltinsSatisfy
    (PLC.AllBuiltinArgs PLC.DefaultUni HasFromBuiltin)
    (Lift PLC.DefaultUni)
