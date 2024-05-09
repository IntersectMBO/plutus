{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeSynonymInstances     #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.IsOpaque where

import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusTx.Base (id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal
import PlutusTx.Builtins.IsBuiltin (FromBuiltin)

import Data.Kind qualified as GHC
import GHC.Magic qualified as Magic

type IsOpaque :: GHC.Type -> GHC.Constraint
class PLC.DefaultUni `PLC.Contains` FromBuiltin a => IsOpaque a where
    type FromOpaque a
    fromOpaque :: a -> FromOpaque a
    toOpaque :: FromOpaque a -> a

instance IsOpaque BuiltinInteger where
    type FromOpaque BuiltinInteger = BuiltinInteger
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance IsOpaque BuiltinByteString where
    type FromOpaque BuiltinByteString = BuiltinByteString
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance IsOpaque BuiltinString where
    type FromOpaque BuiltinString = BuiltinString
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance IsOpaque BuiltinUnit where
    type FromOpaque BuiltinUnit = ()
    {-# INLINABLE fromOpaque #-}
    fromOpaque u = chooseUnit u ()
    {-# INLINABLE toOpaque #-}
    toOpaque x = case x of () -> unitval

instance IsOpaque BuiltinBool where
    type FromOpaque BuiltinBool = Bool
    {-# INLINABLE fromOpaque #-}
    fromOpaque b = ifThenElse b True False
    {-# INLINABLE toOpaque #-}
    toOpaque b = if b then true else false

instance IsOpaque a => IsOpaque (BuiltinList a) where
    type FromOpaque (BuiltinList a) = [FromOpaque a]

    {-# INLINABLE fromOpaque #-}
    fromOpaque = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting
          -- lifted to the top level, which means it gets a proper unfolding, which means that
          -- specialization can work, which can actually help quite a bit here.
          {-# INLINABLE go #-}
          go :: BuiltinList a -> [FromOpaque a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we
          -- need to do the manual laziness ourselves.
          go l = chooseList l (\_ -> []) (\_ -> fromOpaque (head l) : go (tail l)) unitval

    {-# INLINE toOpaque #-}
    toOpaque = goList where
        goList :: [FromOpaque a] -> BuiltinList a
        goList []     = mkNil @(FromBuiltin a) (Magic.inline PLC.knownUni)
        goList (d:ds) = mkCons (toOpaque d) (goList ds)

instance (IsOpaque a, IsOpaque b) => IsOpaque (BuiltinPair a b) where
    type FromOpaque (BuiltinPair a b) = (FromOpaque a, FromOpaque b)
    {-# INLINABLE fromOpaque #-}
    fromOpaque p = (fromOpaque $ fst p, fromOpaque $ snd p)
    {-# INLINABLE toOpaque #-}
    toOpaque (d1, d2) =
        mkPair
            @(FromBuiltin a)
            @(FromBuiltin b)
            (Magic.inline PLC.knownUni)
            (Magic.inline PLC.knownUni)
            (toOpaque d1)
            (toOpaque d2)

instance IsOpaque BuiltinData where
    type FromOpaque BuiltinData = BuiltinData
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance IsOpaque BuiltinBLS12_381_G1_Element where
    type FromOpaque BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_G1_Element a) = a
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_G1_Element

instance IsOpaque BuiltinBLS12_381_G2_Element where
    type FromOpaque BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_G2_Element a) = a
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_G2_Element

instance IsOpaque BuiltinBLS12_381_MlResult where
    type FromOpaque BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_MlResult a) = a
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_MlResult
