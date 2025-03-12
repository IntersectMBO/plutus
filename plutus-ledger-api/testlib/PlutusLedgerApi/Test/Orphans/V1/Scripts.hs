{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Scripts () where

import Data.Coerce (coerce)
import PlutusLedgerApi.Test.Orphans.PlutusTx (Blake2b244Hash (Blake2b244Hash),
                                              Blake2b256Hash (Blake2b256Hash))
import PlutusLedgerApi.V1.Scripts (Datum (Datum), DatumHash (DatumHash), Redeemer (Redeemer),
                                   RedeemerHash (RedeemerHash), ScriptHash (ScriptHash))
import PlutusTx.Prelude
import Test.QuickCheck (Arbitrary, CoArbitrary, Function (function), functionMap)

deriving via BuiltinData instance Arbitrary Redeemer

deriving via BuiltinData instance CoArbitrary Redeemer

instance Function Redeemer where
  {-# INLINEABLE function #-}
  function = functionMap coerce Redeemer


deriving via BuiltinData instance Arbitrary Datum

deriving via BuiltinData instance CoArbitrary Datum

instance Function Datum where
  {-# INLINEABLE function #-}
  function = functionMap coerce Datum


deriving via Blake2b256Hash instance Arbitrary DatumHash

deriving via Blake2b256Hash instance CoArbitrary DatumHash

instance Function DatumHash where
  {-# INLINEABLE function #-}
  function = functionMap coerce DatumHash


deriving via DatumHash instance Arbitrary RedeemerHash

deriving via DatumHash instance CoArbitrary RedeemerHash

instance Function RedeemerHash where
  {-# INLINEABLE function #-}
  function = functionMap coerce RedeemerHash

deriving via Blake2b244Hash instance Arbitrary ScriptHash

deriving via Blake2b244Hash instance CoArbitrary ScriptHash

instance Function ScriptHash where
  {-# INLINEABLE function #-}
  function = functionMap coerce ScriptHash
