{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Core.Instance.Flat () where

import Control.Monad (when)
import PlutusCore qualified as PLC
import PlutusCore.Flat (Flat (..))
import PlutusCore.FlatInstances ()
import PlutusCore.Version (plcVersion130)
import PlutusIR.Core.Plated (usesTryBuiltin)
import PlutusIR.Core.Type

{- Note [Serialization of PIR]
The serialized version of Plutus-IR will be included in  the final
executable for helping debugging and testing and providing better error
reporting. It is not meant to be stored on the chain, which means that
the underlying representation can vary. The `Generic` instances of the
terms can thus be used as backwards compatibility is not required.
-}

deriving anyclass instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Datatype tyname name uni a)

deriving anyclass instance Flat Recursivity

deriving anyclass instance Flat Strictness

deriving anyclass instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Binding tyname name uni fun a)

deriving anyclass instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Term tyname name uni fun a)

instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Program tyname name uni fun a)
  where
  decode = do
    program@(Program _ v t) <- Program <$> decode <*> decode <*> decode
    when (v < plcVersion130 && usesTryBuiltin t) $ fail "'tryBuiltin' requires version 1.3.0"
    pure program
