{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module AsData.Budget.Types where

import PlutusTx.AsData qualified as AsData
import PlutusTx.AsData.Internal (wrapUnsafeDataAsConstr, wrapUnsafeUncons)
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

newtype IntsManual = IntsManualDataCon PlutusTx.BuiltinData
  deriving newtype (PlutusTx.Eq, PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)

pattern IntsManual :: Integer -> Integer -> Integer -> Integer -> IntsManual
pattern IntsManual {int1Manual, int2Manual, int3Manual, int4Manual} <-
  IntsManualDataCon
    ( wrapUnsafeDataAsConstr ->
        BI.snd ->
          wrapUnsafeUncons ->
            ( PlutusTx.unsafeFromBuiltinData -> int1Manual
              , wrapUnsafeUncons ->
                  ( PlutusTx.unsafeFromBuiltinData -> int2Manual
                    , wrapUnsafeUncons ->
                        ( PlutusTx.unsafeFromBuiltinData -> int3Manual
                          , BI.head -> PlutusTx.unsafeFromBuiltinData -> int4Manual
                          )
                    )
              )
      )
  where
    IntsManual a b c d =
      IntsManualDataCon
        ( BI.mkConstr
            0
            ( BI.mkCons
                (PlutusTx.toBuiltinData a)
                ( BI.mkCons
                    (PlutusTx.toBuiltinData b)
                    ( BI.mkCons
                        (PlutusTx.toBuiltinData c)
                        (BI.mkCons (PlutusTx.toBuiltinData d) (BI.mkNilData BI.unitval))
                    )
                )
            )
        )

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
  where
    ThisDManual arg =
      TheseDManual_
        (BI.mkConstr 0 (BI.mkCons (PlutusTx.toBuiltinData arg) (BI.mkNilData BI.unitval)))

pattern ThatDManual :: (PlutusTx.ToData b, PlutusTx.UnsafeFromData b) => b -> TheseDManual a b
pattern ThatDManual arg <-
  TheseDManual_
    (BI.unsafeDataAsConstr -> B.pairToPair -> ((PlutusTx.==) 1 -> True, unpack1 -> arg))
  where
    ThatDManual arg =
      TheseDManual_
        (BI.mkConstr 1 (BI.mkCons (PlutusTx.toBuiltinData arg) (BI.mkNilData BI.unitval)))

unpack1 :: PlutusTx.UnsafeFromData a => BI.BuiltinList BI.BuiltinData -> a
unpack1 =
  PlutusTx.unsafeFromBuiltinData . BI.head

pattern TheseDManual
  :: ( PlutusTx.ToData a
     , PlutusTx.UnsafeFromData a
     , PlutusTx.ToData b
     , PlutusTx.UnsafeFromData b
     )
  => a -> b -> TheseDManual a b
pattern TheseDManual arg1 arg2 <-
  TheseDManual_
    (BI.unsafeDataAsConstr -> B.pairToPair -> ((PlutusTx.==) 2 -> True, unpack2 -> (arg1, arg2)))
  where
    TheseDManual arg1 arg2 =
      TheseDManual_
        ( BI.mkConstr
            2
            ( BI.mkCons
                (PlutusTx.toBuiltinData arg1)
                ( BI.mkCons
                    (PlutusTx.toBuiltinData arg2)
                    (BI.mkNilData BI.unitval)
                )
            )
        )

unpack2
  :: (PlutusTx.UnsafeFromData a, PlutusTx.UnsafeFromData b)
  => BI.BuiltinList BI.BuiltinData -> (a, b)
unpack2 args =
  let x = PlutusTx.unsafeFromBuiltinData $ BI.head args
      rest = BI.tail args
      y = PlutusTx.unsafeFromBuiltinData $ BI.head rest
   in (x, y)

{-# COMPLETE ThisDManual, ThatDManual, TheseDManual #-}
