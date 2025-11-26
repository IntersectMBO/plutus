{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module PlutusTx.Lift.TestInstances () where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusTx.Builtins.HasBuiltin
import PlutusTx.Lift.Class

import Data.Kind qualified as GHC

-- | @BuiltinSatisfies pre post a@ holds if @pre (ToBuiltin a)@ implies @post (ToBuiltin a)@.
type BuiltinSatisfies
  :: (GHC.Type -> GHC.Constraint)
  -> (GHC.Type -> GHC.Constraint)
  -> GHC.Type
  -> GHC.Constraint
class (pre (ToBuiltin a) => post (ToBuiltin a)) => BuiltinSatisfies pre post a

instance (pre (ToBuiltin a) => post (ToBuiltin a)) => BuiltinSatisfies pre post a

{-| Test that each built-in type @a@ from 'PLC.DefaultUni' satisfies @post (ToBuiltin a)@ given
@pre (ToBuiltin a)@. -}
type TestAllBuiltinsSatisfy
  :: (GHC.Type -> GHC.Constraint)
  -> (GHC.Type -> GHC.Constraint)
  -> GHC.Constraint
class PLC.DefaultUni `PLC.Everywhere` BuiltinSatisfies pre post => TestAllBuiltinsSatisfy pre post

-- | Test that each built-in type from 'PLC.DefaultUni' has a 'Typeable' instance.
instance
  TestAllBuiltinsSatisfy
    (PLC.AllBuiltinArgs PLC.DefaultUni (Typeable PLC.DefaultUni))
    (Typeable PLC.DefaultUni)

{-| Test that each built-in type from 'PLC.DefaultUni' has a 'Lift' instance. Since the 'Lift'
instances are defined in terms of 'fromBuiltin', this also tests that each built-in type has a
'FromBuiltin' instance. Which in turn requires a 'ToBuiltin' instance to exist due to the
superclass constraint, so this is implicitly tested as well. -}
instance
  TestAllBuiltinsSatisfy
    (PLC.AllBuiltinArgs PLC.DefaultUni HasFromBuiltin)
    (Lift PLC.DefaultUni)
