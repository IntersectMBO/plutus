{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Constitution.Config.Instance.TxLift () where

import Cardano.Constitution.Config.Types
import Language.Haskell.TH as TH
import PlutusCore.Default as Tx (DefaultUni)
import PlutusTx.Lift as Tx
import PlutusTx.Lift.Class as Tx

-- `Tx.makeLift` depends on TH which is sensitive to re-ordering; try to NOT reorder the following.
----------

Tx.makeLift ''PredKey

deriving newtype instance
  (Tx.Typeable Tx.DefaultUni predValue, Tx.Lift Tx.DefaultUni predValue)
  => Tx.Lift Tx.DefaultUni (Predicates predValue)

Tx.makeTypeable (TH.ConT ''Tx.DefaultUni) ''Predicates
Tx.makeLift ''ParamValue
Tx.makeLift ''ConstitutionConfig
