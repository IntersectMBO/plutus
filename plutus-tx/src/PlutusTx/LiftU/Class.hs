{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module PlutusTx.LiftU.Class where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Data
import PlutusCore.MkPlc qualified as PLC
import PlutusTx.Builtins
import PlutusTx.Builtins.Class (FromBuiltin (..))
import PlutusTx.Builtins.Internal (BuiltinInteger, BuiltinList)
import UntypedPlutusCore qualified as UPLC

import Data.ByteString qualified as BS
import Data.Text qualified as Text

import Prelude

class LiftU name uni fun a where
  -- | Lift a value into Untyped Plutus Core.
  liftU :: a -> UPLC.Term name uni fun ()

liftUBuiltin
    :: forall a name uni fun. uni `PLC.Includes` a
    => a -> UPLC.Term name uni fun ()
liftUBuiltin = PLC.mkConstant ()

instance uni `PLC.Includes` Integer => LiftU name uni fun BuiltinInteger where
    liftU b = liftUBuiltin $ fromBuiltin b

instance uni `PLC.Includes` Data => LiftU name uni fun BuiltinData where
    liftU d = liftUBuiltin (builtinDataToData d)

instance uni `PLC.Includes` BS.ByteString => LiftU name uni fun BuiltinByteString where
    liftU b = liftUBuiltin $ fromBuiltin b

instance uni `PLC.Includes` Text.Text => LiftU name uni fun BuiltinString where
    liftU b = liftUBuiltin $ fromBuiltin b

instance (FromBuiltin arep a, uni `PLC.Includes` [a]) => LiftU name uni fun (BuiltinList arep) where
    liftU b = liftUBuiltin $ fromBuiltin b

class UnliftU name uni fun a where
  -- | Unlift a value from Untyped Plutus Core.
  unliftU :: UPLC.Term name uni fun () -> Maybe a

unliftUBuiltin
    :: forall a name uni fun
    . (PLC.ReadKnownIn uni (UPLC.Term name uni fun ()) a)
    => UPLC.Term name uni fun () -> Maybe a
unliftUBuiltin t = case PLC.readKnown t of
  Left _  -> Nothing
  Right v -> Just v

instance (PLC.ReadKnownIn uni (UPLC.Term name uni fun ()) Integer)
    => UnliftU name uni fun BuiltinInteger where
    unliftU t = toBuiltin <$> unliftUBuiltin @Integer t

instance (PLC.ReadKnownIn uni (UPLC.Term name uni fun ()) Data)
    => UnliftU name uni fun BuiltinData where
    unliftU t = dataToBuiltinData <$> unliftUBuiltin t

instance (PLC.ReadKnownIn uni (UPLC.Term name uni fun ()) BS.ByteString)
    => UnliftU name uni fun BuiltinByteString where
    unliftU t = toBuiltin <$> unliftUBuiltin @BS.ByteString t

instance (PLC.ReadKnownIn uni (UPLC.Term name uni fun ()) Text.Text)
    => UnliftU name uni fun BuiltinString where
    unliftU t = toBuiltin <$> unliftUBuiltin @Text.Text t

-- FIXME
--instance (ToBuiltin a arep, PLC.ReadKnownIn uni (UPLC.Term UPLC.Name uni fun ()) [a])
--    => UnliftU uni fun (BuiltinList arep) where
    --unliftU t = toBuiltin <$> unliftUBuiltin @[a] t
