{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Typeclasses.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import           Plugin.Data.Spec

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin
import qualified Language.PlutusTx.Prelude  as P

import           Plugin.Typeclasses.Lib

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

typeclasses :: TestNested
typeclasses = testNested "Typeclasses" [
    goldenPir "sizedBasic" sizedBasic
    , goldenPir "sizedPair" sizedPair
    , goldenPir "multiFunction" multiFunction
    , goldenPir "defaultMethods" defaultMethods
  ]

class Sized a where
    size :: a -> Integer

instance Sized Integer where
    size x = x

instance (Sized a, Sized b) => Sized (a, b) where
    {-# INLINABLE size #-}
    size (a, b) = size a `Builtins.addInteger` size b

sizedBasic :: CompiledCode (Integer -> Integer)
sizedBasic = plc @"sizedBasic" (\(a::Integer) -> size a)

sizedPair :: CompiledCode (Integer -> Integer -> Integer)
sizedPair = plc @"sizedPair" (\(a::Integer) (b::Integer) -> size (a, b))

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
multiFunction = plc @"multiFunction" (
    let
        {-# NOINLINE predicate #-}
        predicate :: (PersonLike p) => p -> Bool
        predicate p = likesAnimal p Cat P.&& (age p `Builtins.greaterThanInteger` 30)
    in \(p::Person) -> predicate p)

defaultMethods :: CompiledCode (Integer -> Integer)
defaultMethods = plc @"defaultMethods" (
    let
        {-# NOINLINE f #-}
        f :: (DefaultMethods a) => a -> Integer
        f a = method2 a
    in \(a::Integer) -> f a)
