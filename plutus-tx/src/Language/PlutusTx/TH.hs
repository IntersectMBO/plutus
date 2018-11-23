{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Language.PlutusTx.TH (
    plutus,
    plutusUntyped,
    PlcCode,
    getSerializedCode,
    getAst) where

import           Language.PlutusTx.Plugin

import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program.
plutus :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp PlcCode)
-- See note [Typed TH]
plutus e = TH.unsafeTExpCoerce $ plutusUntyped $ TH.unType <$> e

{- Note [Typed TH]
It's nice to use typed TH! However, we sadly can't *quite* use it thoroughly, because we
want to make a type literal, and there's no way to do that properly with typed TH.

Moreover, we really want to create an expression with the precise form that we want,
so we can't isolate the badness much. So we pretty much just have to use unsafeTExpCoerce
and assert that we know what we're doing.

This isn't so bad, since our plc function accepts an argument of any type, so that's always
going to typecheck, and the result is always a PlcCode, so that's also fine.
-}

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program.
plutusUntyped :: TH.Q TH.Exp -> TH.Q TH.Exp
plutusUntyped e = do
    TH.addCorePlugin "Language.PlutusTx.Plugin"
    loc <- TH.location
    let locStr = TH.pprint loc
    -- See note [Typed TH]
    [| plc @($(TH.litT $ TH.strTyLit locStr)) $(e) |]
