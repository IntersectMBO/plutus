{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Test.Orphans where

import Prelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Pretty (Pretty, PrettyConst)
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Test (ToTPlc (..), ToUPlc (..), catchAll)
import PlutusIR.Analysis.Builtins qualified as PIR
import PlutusIR.Test ()
import PlutusIR.Transform.RewriteRules qualified as PIR
import PlutusPrelude (Default)
import PlutusTx.Code (CompiledCodeIn, getPir, getPlcNoAnn)

import PlutusCore.Flat (Flat)
import Test.Tasty.Extras ()

instance
  (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => ToUPlc (CompiledCodeIn uni fun a) uni fun
  where
  toUPlc compiledCode = toUPlc =<< catchAll (getPlcNoAnn compiledCode)

instance
  ( PLC.PrettyParens (PLC.SomeTypeIn uni)
  , PLC.GEq uni
  , PLC.Typecheckable uni fun
  , PLC.CaseBuiltin uni
  , PLC.Closed uni
  , uni `PLC.Everywhere` PrettyConst
  , Pretty fun
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Default (PLC.CostingPart uni fun)
  , Default (PIR.BuiltinsInfo uni fun)
  , Default (PIR.RewriteRules uni fun)
  )
  => ToTPlc (CompiledCodeIn uni fun a) uni fun
  where
  toTPlc compiledCode =
    catchAll (getPir compiledCode) >>= \case
      Nothing -> fail "No PIR available"
      Just program -> toTPlc program
