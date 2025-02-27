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
import PlutusTx.Builtins qualified as B
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

AsData.asData
  [d|
    data TheseD a b
      = ThisD a
      | ThatD b
      | TheseD a b
      deriving newtype (PlutusTx.Eq, PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
  |]

newtype TheseDManual a b = TheseDManual_ PlutusTx.BuiltinData
  deriving newtype (PlutusTx.Eq, PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)

pattern ThisDManual :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> TheseDManual a b
pattern ThisDManual arg <-
  TheseDManual_
    (BI.unsafeDataAsConstr -> B.pairToPair -> ((PlutusTx.==) 0 -> True, unpack1 -> arg))
  where ThisDManual arg =
          TheseDManual_
            (BI.mkConstr 0 (BI.mkCons (PlutusTx.toBuiltinData arg) (BI.mkNilData BI.unitval)))

pattern ThatDManual :: (PlutusTx.ToData b, PlutusTx.UnsafeFromData b) => b -> TheseDManual a b
pattern ThatDManual arg <-
  TheseDManual_
    (BI.unsafeDataAsConstr -> B.pairToPair -> ((PlutusTx.==) 0 -> True, unpack1 -> arg))
  where ThatDManual arg =
          TheseDManual_
            (BI.mkConstr 1 (BI.mkCons (PlutusTx.toBuiltinData arg) (BI.mkNilData BI.unitval)))

unpack1 :: PlutusTx.UnsafeFromData a => BI.BuiltinList BI.BuiltinData -> a
unpack1 =
  PlutusTx.unsafeFromBuiltinData . BI.head

pattern TheseDManual
  :: (PlutusTx.ToData a
    , PlutusTx.UnsafeFromData a
    , PlutusTx.ToData b
    , PlutusTx.UnsafeFromData b
    ) => a -> b -> TheseDManual a b
pattern TheseDManual arg1 arg2 <-
  TheseDManual_
    (BI.unsafeDataAsConstr -> B.pairToPair -> ((PlutusTx.==) 2 -> True, unpack2 -> (arg1, arg2)))
  where TheseDManual arg1 arg2 =
          TheseDManual_
            (BI.mkConstr 2
              (BI.mkCons
                (PlutusTx.toBuiltinData arg1)
                (BI.mkCons
                  (PlutusTx.toBuiltinData arg2)
                  (BI.mkNilData BI.unitval)
                )
              )
            )

unpack2
  :: (PlutusTx.UnsafeFromData a, PlutusTx.UnsafeFromData b)
  => BI.BuiltinList BI.BuiltinData -> (a, b)
unpack2 args =
  let ~x = PlutusTx.unsafeFromBuiltinData $ BI.head args
      ~rest = BI.tail args
      ~y = PlutusTx.unsafeFromBuiltinData $ BI.head rest
   in (x, y)


{-# COMPLETE ThisDManual, ThatDManual, TheseDManual #-}
