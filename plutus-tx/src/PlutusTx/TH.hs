{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module PlutusTx.TH (
    compile,
    compileUntyped) where

import           Data.Proxy
import           PlutusTx.Code
import           PlutusTx.Plugin.Utils

import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH


-- | Compile a quoted Haskell expression into a corresponding Plutus Core program.
compile :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp (CompiledCode a))
-- See note [Typed TH]
compile e = TH.unsafeTExpCoerce $ compileUntyped $ TH.unType <$> e

{- Note [Typed TH]
It's nice to use typed TH! However, we sadly can't *quite* use it thoroughly, because we
want to make a type literal, and there's no way to do that properly with typed TH.

Moreover, we really want to create an expression with the precise form that we want,
so we can't isolate the badness much. So we pretty much just have to use 'unsafeTExpCoerce'
and assert that we know what we're doing.

This isn't so bad, since our plc function accepts an argument of any type, so that's always
going to typecheck, and the result is always a 'CompiledCode', so that's also fine.
-}

-- | Compile a quoted Haskell expression into a corresponding Plutus Core program.
compileUntyped :: TH.Q TH.Exp -> TH.Q TH.Exp
compileUntyped e = do
    TH.addCorePlugin "PlutusTx.Plugin"
    loc <- TH.location
    let locStr = TH.pprint loc
    -- See note [Typed TH]
    [| plc (Proxy :: Proxy $(TH.litT $ TH.strTyLit locStr)) $(e) |]
