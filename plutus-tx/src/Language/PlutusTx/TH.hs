{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Language.PlutusTx.TH (
    module Builtins,
    plutus,
    plutusUntyped,
    PlcCode,
    getSerializedCode,
    getAst) where

import           Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Plugin

import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program.
plutus :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp PlcCode)
plutus e = do
    TH.addCorePlugin "Language.PlutusTx.Plugin"
    loc <- TH.location
    let locStr = TH.pprint loc
    -- See note [Typed TH]
    let
        partial :: TH.Q (TH.TExp (a -> PlcCode))
        partial = TH.unsafeTExpCoerce [| \a -> plc @($(TH.litT $ TH.strTyLit locStr)) a |]
    [|| $$(partial) $$(e) ||]

{- Note [Typed TH]
It's nice to use typed TH! However, we sadly can't *quite* use it thoroughly, because we want to make a type literal,
and there's no way to do that properly with typed TH.

However, we can isolate the badness into as small a box as possible, and then use unsafeTExpCoerce.
-}

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program.
plutusUntyped :: TH.Q TH.Exp -> TH.Q TH.Exp
-- Just force our typed version to accept it and then turn it back into an untyped one. This means it will
-- get typechecked again later, which is good because we lied about knowing the type of the argument.
plutusUntyped e = TH.unType <$> plutus (TH.unsafeTExpCoerce e)
