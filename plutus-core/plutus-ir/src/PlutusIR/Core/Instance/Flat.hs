{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Core.Instance.Flat () where

import PlutusIR.Core.Type

import PlutusCore qualified as PLC
import PlutusCore.Flat (Flat)
import PlutusCore.FlatInstances ()

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

deriving anyclass instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Program tyname name uni fun a)
