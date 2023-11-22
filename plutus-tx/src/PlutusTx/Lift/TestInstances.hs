{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE UndecidableSuperClasses  #-}

module PlutusTx.Lift.TestInstances () where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 as G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 as G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing (MlResult)
import PlutusCore.Data
import PlutusTx.Builtins
import PlutusTx.Builtins.Class (FromBuiltin)
import PlutusTx.Builtins.Internal (BuiltinBool, BuiltinList, BuiltinPair, BuiltinUnit)
import PlutusTx.Lift.Class

import Data.ByteString qualified as BS
import Data.Kind qualified as GHC
import Data.Text qualified as T

import Prelude (Bool)

-- | A class for converting each type from the universe to its @Builtin*@ counterpart. E.g.
-- 'Bool' to 'BuiltinBool'.
type IsBuiltin :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Constraint
class FromBuiltin (AsBuiltin uni a) a => IsBuiltin uni a where
    type AsBuiltin uni a

type BuiltinSatisfies
    :: (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Type)
    -> GHC.Type
    -> GHC.Constraint
class    (pre a => post (AsBuiltin uni a)) => BuiltinSatisfies pre post uni a
instance (pre a => post (AsBuiltin uni a)) => BuiltinSatisfies pre post uni a

type MemberOrGo :: forall a. (a -> GHC.Constraint) -> [a] -> a -> GHC.Constraint
type family MemberOrGo constr xs x where
    MemberOrGo constr '[]       x = constr x
    MemberOrGo constr (x ': _)  x = ()
    MemberOrGo constr (_ ': xs) x = MemberOrGo constr xs x

-- | @MemberOrGo constr xs x@ means that either @x@ is a member of @xs@ or @constr xs@ holds.
type MemberOr :: forall a. (a -> GHC.Constraint) -> [a] -> a -> GHC.Constraint
class    MemberOrGo constr xs x => MemberOr constr xs x
instance MemberOrGo constr xs x => MemberOr constr xs x

type AllBuiltinsSatisfyExcluding
    :: [GHC.Type]
    -> (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Constraint)
    -> (GHC.Type -> GHC.Type)
    -> GHC.Constraint
class uni `PLC.Everywhere` MemberOr (BuiltinSatisfies pre post uni) excl =>
    AllBuiltinsSatisfyExcluding excl pre post uni

class    Typeable uni (AsBuiltin uni a) => TypeableBuiltin uni a
instance Typeable uni (AsBuiltin uni a) => TypeableBuiltin uni a

class    (PLC.AllBuiltinArgs uni (TypeableBuiltin uni) a, uni `PLC.HasTypeLevel` a) =>
    TypeablePre uni a
instance (PLC.AllBuiltinArgs uni (TypeableBuiltin uni) a, uni `PLC.HasTypeLevel` a) =>
    TypeablePre uni a

class    (PLC.AllBuiltinArgs uni (IsBuiltin uni) a, uni `PLC.HasTermLevel` a) => LiftPre uni a
instance (PLC.AllBuiltinArgs uni (IsBuiltin uni) a, uni `PLC.HasTermLevel` a) => LiftPre uni a

--------------------

instance IsBuiltin PLC.DefaultUni Integer where
    type AsBuiltin PLC.DefaultUni Integer = Integer
instance IsBuiltin PLC.DefaultUni BS.ByteString where
    type AsBuiltin PLC.DefaultUni BS.ByteString = BuiltinByteString
instance IsBuiltin PLC.DefaultUni T.Text where
    type AsBuiltin PLC.DefaultUni T.Text = BuiltinString
instance IsBuiltin PLC.DefaultUni () where
    type AsBuiltin PLC.DefaultUni () = BuiltinUnit
instance IsBuiltin PLC.DefaultUni Bool where
    type AsBuiltin PLC.DefaultUni Bool = BuiltinBool
instance IsBuiltin PLC.DefaultUni a => IsBuiltin PLC.DefaultUni [a] where
    type AsBuiltin PLC.DefaultUni [a] = BuiltinList (AsBuiltin PLC.DefaultUni a)
instance (IsBuiltin PLC.DefaultUni a, IsBuiltin PLC.DefaultUni b) =>
        IsBuiltin PLC.DefaultUni (a, b) where
    type AsBuiltin PLC.DefaultUni (a, b) =
        BuiltinPair (AsBuiltin PLC.DefaultUni a) (AsBuiltin PLC.DefaultUni b)
-- No instance for 'Data', because there's no 'FromBuiltin' instance for 'Data'
-- (we could add @FromBuiltin Data Data@, but it would be weird to have a pointless instance just
-- for the tests here).
instance IsBuiltin PLC.DefaultUni G1.Element where
    type AsBuiltin PLC.DefaultUni G1.Element = BuiltinBLS12_381_G1_Element
instance IsBuiltin PLC.DefaultUni G2.Element where
    type AsBuiltin PLC.DefaultUni G2.Element = BuiltinBLS12_381_G2_Element
instance IsBuiltin PLC.DefaultUni MlResult where
    type AsBuiltin PLC.DefaultUni MlResult = BuiltinBLS12_381_MlResult

instance AllBuiltinsSatisfyExcluding
    '[Data] (LiftPre PLC.DefaultUni) (Lift PLC.DefaultUni) PLC.DefaultUni
instance AllBuiltinsSatisfyExcluding
    '[Data] (TypeablePre PLC.DefaultUni) (Typeable PLC.DefaultUni) PLC.DefaultUni
