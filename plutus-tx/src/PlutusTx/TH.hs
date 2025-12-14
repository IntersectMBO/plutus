{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module PlutusTx.TH
  ( compile
  , compileUntyped
  , loadFromFile
  ) where

import Data.Proxy
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH
import PlutusTx.Code
import PlutusTx.Plugin.Utils

-- We do not use qualified import because the whole module contains off-chain code
import Control.Monad.IO.Class
import Data.ByteString qualified as BS
import Prelude

-- | Compile a quoted Haskell expression into a corresponding Plutus Core program.
compile :: TH.Code TH.Q a -> TH.Code TH.Q (CompiledCode a)
-- See Note [Typed TH]
compile e = TH.unsafeCodeCoerce $ compileUntyped $ TH.unType <$> TH.examineCode e

-- | Load a 'CompiledCode' from a file. Drop-in replacement for 'compile'.
loadFromFile :: FilePath -> TH.Code TH.Q (CompiledCode a)
loadFromFile fp = TH.liftCode $ do
  -- We don't have a 'Lift' instance for 'CompiledCode' (we could but it would be tedious),
  -- so we lift the bytestring and construct the value in the quote.
  bs <- liftIO $ BS.readFile fp
  TH.examineCode [||SerializedCode bs Nothing mempty||]

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
  -- See Note [Typed TH]
  [|plc (Proxy :: Proxy $(TH.litT $ TH.strTyLit locStr)) $(e)|]
