{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}

module Plugin.Typeclasses.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Data.Spec
import           Plugin.Lib
import           Plugin.Typeclasses.Lib

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin
import qualified Language.PlutusTx.Prelude    as P

import qualified Language.PlutusCore.Builtins as PLC
import qualified Language.PlutusCore.Universe as PLC

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

compareTest :: CompiledCode (Ordering)
compareTest = plc (Proxy @"compareTest") (opCompare (1::Integer) (2::Integer))
