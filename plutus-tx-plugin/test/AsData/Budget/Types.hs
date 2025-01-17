{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module AsData.Budget.Types where

import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx

AsData.asData
  [d|
    data Ints = Ints
      { int1 :: Integer
      , int2 :: Integer
      , int3 :: Integer
      , int4 :: Integer
      }
      deriving newtype (PlutusTx.Eq, PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

-- | This is a manually implemented `AsData`, with field accessors that are
-- more friendly to CSE. We should generate field accessors like these in TH.
newtype IntsManual = IntsManual PlutusTx.BuiltinData
  deriving newtype
    ( PlutusTx.Eq
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    , PlutusTx.ToData
    )

pattern IntsManualPattern :: Integer -> Integer -> Integer -> Integer -> IntsManual
pattern IntsManualPattern x y z w <- IntsManual (unpackIntsManual -> (x, y, z, w))
  where
    IntsManualPattern x y z w = IntsManual (packIntsManual x y z w)

-- Improvements over the TH-generated pattern synonym:
-- 1. Since this is a product type, there's no need to check `BI.fst tup == 0`
-- 2. Don't use `pairToPair` or `unsafeUncons`, since they construct non-builtin pairs.
unpackIntsManual :: PlutusTx.BuiltinData -> (Integer, Integer, Integer, Integer)
unpackIntsManual d =
  let tup = BI.unsafeDataAsConstr d
      ds0 = BI.snd tup
      ds1 = BI.tail ds0
      ds2 = BI.tail ds1
      ds3 = BI.tail ds2
      x = PlutusTx.unsafeFromBuiltinData (BI.head ds0)
      y = PlutusTx.unsafeFromBuiltinData (BI.head ds1)
      z = PlutusTx.unsafeFromBuiltinData (BI.head ds2)
      w = PlutusTx.unsafeFromBuiltinData (BI.head ds3)
   in (x, y, z, w)

packIntsManual :: Integer -> Integer -> Integer -> Integer -> PlutusTx.BuiltinData
packIntsManual x y z w =
  BI.mkConstr
    0
    (BI.mkCons
      (PlutusTx.toBuiltinData x)
      (BI.mkCons
        (PlutusTx.toBuiltinData y)
        (BI.mkCons
          (PlutusTx.toBuiltinData z)
          (BI.mkCons
            (PlutusTx.toBuiltinData w)
            (BI.mkNilData BI.unitval)
          )
        )
      )
    )

int1Manual :: IntsManual -> Integer
int1Manual (IntsManual d) =
  let tup = BI.unsafeDataAsConstr d
      i = BI.fst tup
      ds0 = BI.snd tup
      d0 = BI.head ds0
   in if i PlutusTx.== 0
        then BI.unsafeDataAsI d0
        else PlutusTx.error ()

int2Manual :: IntsManual -> Integer
int2Manual (IntsManual d) =
  let tup = BI.unsafeDataAsConstr d
      i = BI.fst tup
      ds0 = BI.snd tup
      ds1 = BI.tail ds0
      d1 = BI.head ds1
   in if i PlutusTx.== 0
        then BI.unsafeDataAsI d1
        else PlutusTx.error ()

int3Manual :: IntsManual -> Integer
int3Manual (IntsManual d) =
  let tup = BI.unsafeDataAsConstr d
      i = BI.fst tup
      ds0 = BI.snd tup
      ds1 = BI.tail ds0
      ds2 = BI.tail ds1
      d2 = BI.head ds2
   in if i PlutusTx.== 0
        then BI.unsafeDataAsI d2
        else PlutusTx.error ()

int4Manual :: IntsManual -> Integer
int4Manual (IntsManual d) =
  let tup = BI.unsafeDataAsConstr d
      i = BI.fst tup
      ds0 = BI.snd tup
      ds1 = BI.tail ds0
      ds2 = BI.tail ds1
      ds3 = BI.tail ds2
      d3 = BI.head ds3
   in if i PlutusTx.== 0
        then BI.unsafeDataAsI d3
        else PlutusTx.error ()
