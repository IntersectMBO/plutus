{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-typecheck #-}

module Plugin.Typeclasses.Spec where

import Test.Tasty.Extras

import Plugin.Typeclasses.Lib

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Foldable qualified as F
import PlutusTx.List qualified as List
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test
import PlutusTx.Traversable qualified as T

import Data.Proxy

typeclasses :: TestNested
typeclasses =
  testNested "Typeclasses" . pure $
    testNestedGhc
      [ goldenPirReadable "sizedBasic" sizedBasic
      , goldenPirReadable "sizedPair" sizedPair
      , goldenPirReadable "multiFunction" multiFunction
      , goldenPirReadable "defaultMethods" defaultMethods
      , goldenPirReadable "partialApplication" partialApplication
      , goldenPirReadable "sequenceTest" sequenceTest
      , goldenPirReadable "compareTest" compareTest
      , goldenPirReadable "concatTest" concatTest
      , goldenPirReadable "sumTest" sumTest
      , goldenPirReadable "fmapDefaultTest" fmapDefaultTest
      ]

class Sized a where
  size :: a -> Integer

instance Sized Integer where
  size x = x

instance (Sized a, Sized b) => Sized (a, b) where
  {-# INLINEABLE size #-}
  size (a, b) = size a `Builtins.addInteger` size b

sizedBasic :: CompiledCode (Integer -> Integer)
sizedBasic = plc (Proxy @"sizedBasic") (\(a :: Integer) -> size a)

sizedPair :: CompiledCode (Integer -> Integer -> Integer)
sizedPair = plc (Proxy @"sizedPair") (\(a :: Integer) (b :: Integer) -> size (a, b))

-- This has multiple methods, so will have to be passed as a dictionary
class PersonLike a where
  age :: a -> Integer
  likesAnimal :: a -> Animal -> Bool

instance PersonLike Person where
  {-# INLINEABLE age #-}
  age Jim = 30
  age Jane = 35
  {-# INLINEABLE likesAnimal #-}
  likesAnimal Jane Cat = True
  likesAnimal _ _ = False

instance PersonLike Alien where
  {-# INLINEABLE age #-}
  age AlienJim = 300
  age AlienJane = 350
  {-# INLINEABLE likesAnimal #-}
  likesAnimal AlienJane Dog = True
  likesAnimal _ _ = False

multiFunction :: CompiledCode (Person -> Bool)
multiFunction =
  plc
    (Proxy @"multiFunction")
    ( let
        {-# OPAQUE predicate #-}
        predicate :: PersonLike p => p -> Bool
        predicate p = likesAnimal p Cat P.&& (age p `Builtins.lessThanInteger` 30)
       in
        \(p :: Person) -> predicate p
    )

defaultMethods :: CompiledCode (Integer -> Integer)
defaultMethods =
  plc
    (Proxy @"defaultMethods")
    ( let
        {-# OPAQUE f #-}
        f :: DefaultMethods a => a -> Integer
        f a = method2 a
       in
        \(a :: Integer) -> f a
    )

partialApplication :: CompiledCode (Integer -> Integer -> Ordering)
partialApplication = plc (Proxy @"partialApplication") (P.compare @Integer)

sequenceTest :: CompiledCode (Maybe [Integer])
sequenceTest = plc (Proxy @"sequenceTests") (T.sequence [Just (1 :: Integer), Just (2 :: Integer)])

opCompare :: P.Ord a => a -> a -> Ordering
opCompare a b = case P.compare a b of
  LT -> GT
  EQ -> EQ
  GT -> LT

compareTest :: CompiledCode Ordering
compareTest = plc (Proxy @"compareTest") (opCompare (1 :: Integer) (2 :: Integer))

concatTest :: CompiledCode [Integer]
concatTest = plc (Proxy @"concatTest") (List.concat [[(1 :: Integer), 2], [3, 4]])

sumTest :: CompiledCode Integer
sumTest = plc (Proxy @"sumTest") (F.sum [(1 :: Integer), 2, 3, 4])

fmapDefaultTest :: CompiledCode [Integer]
fmapDefaultTest = plc (Proxy @"fmapDefaultTest") (T.fmapDefault (P.+ 1) [(1 :: Integer), 2, 3, 4])
