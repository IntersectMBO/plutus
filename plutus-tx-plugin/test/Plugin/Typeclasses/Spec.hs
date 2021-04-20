{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin -fplugin-opt PlutusTx.Plugin:defer-errors -fplugin-opt PlutusTx.Plugin:no-context -fplugin-opt PlutusTx.Plugin:dont-typecheck #-}

module Plugin.Typeclasses.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Data.Spec
import           Plugin.Lib
import           Plugin.Typeclasses.Lib

import qualified PlutusTx.Builtins      as Builtins
import           PlutusTx.Code
import           PlutusTx.Plugin
import qualified PlutusTx.Prelude       as P

import qualified PlutusCore.Builtins    as PLC
import qualified PlutusCore.Universe    as PLC

import           Data.Proxy

typeclasses :: TestNested
typeclasses = testNested "Typeclasses" [
    goldenPir "sizedBasic" sizedBasic
    , goldenPir "sizedPair" sizedPair
    , goldenPir "multiFunction" multiFunction
    , goldenPir "defaultMethods" defaultMethods
    , goldenPir "partialApplication" partialApplication
    , goldenPir "sequenceTest" sequenceTest
    , goldenPir "compareTest" compareTest
    , goldenPir "concatTest" concatTest
    , goldenPir "sumTest" sumTest
    , goldenPir "fmapDefaultTest" fmapDefaultTest
  ]

class Sized a where
    size :: a -> Integer

instance Sized Integer where
    size x = x

instance (Sized a, Sized b) => Sized (a, b) where
    {-# INLINABLE size #-}
    size (a, b) = size a `Builtins.addInteger` size b

sizedBasic :: CompiledCode (Integer -> Integer)
sizedBasic = plc (Proxy @"sizedBasic") (\(a::Integer) -> size a)

sizedPair :: CompiledCode (Integer -> Integer -> Integer)
sizedPair = plc (Proxy @"sizedPair") (\(a::Integer) (b::Integer) -> size (a, b))

-- This has multiple methods, so will have to be passed as a dictionary
class PersonLike a where
    age :: a -> Integer
    likesAnimal :: a -> Animal -> Bool

instance PersonLike Person where
    {-# INLINABLE age #-}
    age Jim  = 30
    age Jane = 35
    {-# INLINABLE likesAnimal #-}
    likesAnimal Jane Cat = True
    likesAnimal _ _      = False

instance PersonLike Alien where
    {-# INLINABLE age #-}
    age AlienJim  = 300
    age AlienJane = 350
    {-# INLINABLE likesAnimal #-}
    likesAnimal AlienJane Dog = True
    likesAnimal _ _           = False

multiFunction :: CompiledCode (Person -> Bool)
multiFunction = plc (Proxy @"multiFunction") (
    let
        {-# NOINLINE predicate #-}
        predicate :: (PersonLike p) => p -> Bool
        predicate p = likesAnimal p Cat P.&& (age p `Builtins.greaterThanInteger` 30)
    in \(p::Person) -> predicate p)

defaultMethods :: CompiledCode (Integer -> Integer)
defaultMethods = plc (Proxy @"defaultMethods") (
    let
        {-# NOINLINE f #-}
        f :: (DefaultMethods a) => a -> Integer
        f a = method2 a
    in \(a::Integer) -> f a)

partialApplication :: CompiledCode (Integer -> Integer -> Ordering)
partialApplication = plc (Proxy @"partialApplication") (P.compare @Integer)

sequenceTest :: CompiledCode (Maybe [Integer])
sequenceTest = plc (Proxy @"sequenceTests") (P.sequence [Just (1 :: Integer), Just (2 :: Integer)])

opCompare :: P.Ord a => a -> a -> Ordering
opCompare a b = case P.compare a b of
    LT -> GT
    EQ -> EQ
    GT -> LT

compareTest :: CompiledCode Ordering
compareTest = plc (Proxy @"compareTest") (opCompare (1::Integer) (2::Integer))

concatTest :: CompiledCode [Integer]
concatTest = plc (Proxy @"concatTest") (P.concat [[(1 :: Integer), 2], [3, 4]])

sumTest :: CompiledCode Integer
sumTest = plc (Proxy @"sumTest") (P.sum [(1 :: Integer), 2, 3, 4])

fmapDefaultTest :: CompiledCode [Integer]
fmapDefaultTest = plc (Proxy @"fmapDefaultTest") (P.fmapDefault (P.+ 1) [(1 :: Integer), 2, 3, 4])
