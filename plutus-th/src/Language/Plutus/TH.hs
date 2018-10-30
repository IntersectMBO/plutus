{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Language.Plutus.TH (plutus, PlcCode, getSerializedCode, getAst, applyPlc) where

import           Language.Plutus.CoreToPLC.Plugin

import qualified Language.Haskell.TH              as TH

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program. Produces an expression of type
-- 'PlcCode'.
plutus :: TH.Q TH.Exp -> TH.Q TH.Exp
-- We would like to do `addCorePlugin "Language.Plutus.CoreToPLC.Plugin"``, but this needs template-haskell-2.13.0.0,
-- which is in the next LTS snapshot.
plutus e = do
    loc <- TH.location
    let locStr = TH.pprint loc
    [| plc @($(TH.litT $ TH.strTyLit locStr)) $(e) |]

{- Note [Typed TH]
It would be nice to have a typed TH version of `plutus`. However, this is hard to do because the singleton type
is not known until TH runtime.

We could cheat and use `unsafeTExpCoerce`, but I'd prefer not to do that unless we have to.
-}
